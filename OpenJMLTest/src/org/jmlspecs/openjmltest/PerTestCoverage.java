package org.jmlspecs.openjmltest;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.lang.reflect.Method;
import java.util.HashSet;
import java.util.Set;

/** Splits JaCoCo coverage by test case (make cov-test-by-test): each test's own coverage is
 *  written to its own .exec file in a per-test directory, instead of everything accumulating
 *  into one destfile for the whole run (what make cov-test does). The same mechanism as
 *  jSMTLIB's and KotlinSL's per-test coverage.
 *
 *  Mechanism: JaCoCo's runtime API ({@code org.jacoco.agent.rt.RT.getAgent()}) exposes
 *  {@code getExecutionData(reset)} and {@code dump(reset)}, which read out -- and zero --
 *  the probe counters of the running JVM. So:
 *  <ul>
 *  <li>at {@link #start}, whatever ran since the previous test (class loading, static
 *      initializers, @BeforeClass and @Parameters methods) is dumped, with a reset, to the
 *      agent's own destfile (setup-coverage points that at _outside-tests.exec);</li>
 *  <li>at {@link #finish}, the counters -- now exactly this one test's coverage -- are read
 *      out, with a reset, and appended to that test's own file.</li>
 *  </ul>
 *  Anything left after the last test is written to _outside-tests.exec by the agent's own
 *  shutdown hook, as usual.
 *
 *  Child JVMs (the openjml scripts run by RunBase's ./run scripts) cannot be reset from here.
 *  Their agent string (OPENJML_JVM, from setup-coverage) has a @COV_TEST@ placeholder in its
 *  destfile, which {@link #childAgent} replaces with the current test's file stem, so each
 *  child appends its own session to the file of the test that launched it. JaCoCo's exec
 *  format is a sequence of blocks, so several sessions appended to one file read back (and
 *  merge) as a single data set. The current test is kept in this JVM, not in a shared file,
 *  because runpar runs several test JVMs at once.
 *
 *  Each JVM writes its own index (setup-coverage names it index-unit-&lt;first suite&gt;.tsv),
 *  mapping each file back to its test (class, display name, outcome, wall-clock ms), since
 *  the file stems are sanitized names; make cov-analyze-by-test concatenates them.
 *
 *  JaCoCo is reached only reflectively, so this class compiles and loads without the agent
 *  jar on the classpath; if no agent is attached it disables itself with a warning. Tests
 *  must run sequentially within the JVM -- the counters are per JVM -- as
 *  OpenJMLTestRunner does. A test that times out may keep running in the background, and
 *  its later coverage is then credited to the following tests.
 */
public class PerTestCoverage {

    /** Agent session id and file stem for everything that runs outside any test. */
    static final String OUTSIDE_TESTS = "_outside-tests";

    /** The placeholder in a child JVM's agent string for the current test's file stem. */
    static final String PLACEHOLDER = "@COV_TEST@";

    /** The instance for this JVM, or null if per-test coverage is off. */
    private static PerTestCoverage instance;

    private final File dir;
    private final PrintWriter index;
    private final Object agent;
    private final Method getExecutionData;
    private final Method dump;
    private final Method setSessionId;

    private final String cwdPrefix = new File(System.getProperty("user.dir")).getAbsolutePath() + File.separator;
    private final Set<String> usedStems = new HashSet<String>();
    private volatile String currentStem;
    private long startMillis;

    /** Starts per-test coverage if setup-coverage asked for it (COV_BY_TEST_DIR and
     *  COV_BY_TEST_INDEX set) and a JaCoCo agent is attached; returns the instance, or null. */
    public static PerTestCoverage init() throws IOException {
        String dir = System.getenv("COV_BY_TEST_DIR");
        String indexFile = System.getenv("COV_BY_TEST_INDEX");
        if (dir == null || dir.isEmpty() || indexFile == null || indexFile.isEmpty()) return null;
        Object agent;
        try {
            Class<?> rt = Class.forName("org.jacoco.agent.rt.RT");
            agent = rt.getMethod("getAgent").invoke(null);
        } catch (ReflectiveOperationException | LinkageError e) {
            System.err.println("WARNING: per-test coverage requested but no JaCoCo agent is attached ("
                    + e + "); per-test coverage disabled");
            return null;
        }
        instance = new PerTestCoverage(new File(dir), new File(indexFile), agent);
        return instance;
    }

    private PerTestCoverage(File dir, File indexFile, Object agent) throws IOException {
        this.dir = dir;
        this.agent = agent;
        try {
            // Looked up on the public interface, not agent.getClass(): the agent's
            // implementation class is package-private, so its own Method objects
            // aren't invocable from here.
            Class<?> iAgent = Class.forName("org.jacoco.agent.rt.IAgent");
            getExecutionData = iAgent.getMethod("getExecutionData", boolean.class);
            dump = iAgent.getMethod("dump", boolean.class);
            setSessionId = iAgent.getMethod("setSessionId", String.class);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("unexpected JaCoCo agent API", e);
        }
        dir.mkdirs();
        index = new PrintWriter(new FileWriter(indexFile), true);
        index.println("file\tclass\tdisplayName\tstatus\tmillis");
        setSession(OUTSIDE_TESTS);
    }

    /** Called just before a test runs; [suite] is the test class, [name] the method name
     *  plus any parameters. */
    public void start(Class<?> suite, String name) {
        invoke(dump, true); // everything since the previous test goes to _outside-tests.exec
        currentStem = uniqueStem(suite, name);
        startMillis = System.currentTimeMillis();
        setSession(currentStem);
    }

    /** Called when the test is over; [status] is PASS, FAIL or TIMEOUT. */
    public void finish(Class<?> suite, String name, String status) throws IOException {
        long millis = System.currentTimeMillis() - startMillis;
        byte[] data = (byte[]) invoke(getExecutionData, true);
        String file = currentStem + ".exec";
        // Append, not overwrite: this test's child JVMs (if any) have already written
        // their own sessions to this same file.
        try (OutputStream out = new FileOutputStream(new File(dir, file), true)) {
            out.write(data);
        }
        index.println(file + "\t" + suite.getName() + "\t" + suite.getSimpleName() + "." + name
                + "\t" + status + "\t" + millis);
        setSession(OUTSIDE_TESTS);
        currentStem = null;
    }

    /** The agent string for a child JVM: [agentString] (OPENJML_JVM, from setup-coverage) with
     *  the placeholder replaced by the current test's file stem -- or _unattributed, outside any
     *  test. Unchanged when per-test coverage is off or the string has no placeholder. */
    public static String childAgent(String agentString) {
        if (agentString == null || !agentString.contains(PLACEHOLDER)) return agentString;
        PerTestCoverage p = instance;
        String stem = p != null && p.currentStem != null ? p.currentStem : "_unattributed";
        return agentString.replace(PLACEHOLDER, stem);
    }

    /** A file stem for the test, unique within this run: the test class's simple name plus the
     *  method name and parameters, reduced to filename-safe characters. Parameters that carry
     *  an absolute path lose the working-directory prefix, so stems are the same on every
     *  machine and checkout. Two names that sanitize to the same stem get a numeric suffix. */
    private String uniqueStem(Class<?> suite, String name) {
        String base = sanitize(suite.getSimpleName() + "." + name.replace(cwdPrefix, ""));
        String stem = base;
        for (int n = 2; !usedStems.add(stem); n++) {
            stem = base + "~" + n;
        }
        return stem;
    }

    static String sanitize(String s) {
        String r = s.replaceAll("[^A-Za-z0-9._-]+", "_");
        // Keep stems comfortably under common 255-byte filename limits.
        return r.length() > 180 ? r.substring(0, 180) : r;
    }

    private void setSession(String id) {
        invoke(setSessionId, id);
    }

    private Object invoke(Method m, Object arg) {
        try {
            return m.invoke(agent, arg);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("JaCoCo agent call " + m.getName() + " failed", e);
        }
    }
}
