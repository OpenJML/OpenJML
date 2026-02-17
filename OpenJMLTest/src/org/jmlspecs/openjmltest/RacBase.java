package org.jmlspecs.openjmltest;

import static org.junit.Assert.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.Strings;
import org.junit.Before;
import org.junit.BeforeClass;
import org.openjml.MockJavaFileObject;

import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

/** This is a base class for unit test files that exercise the RAC.
 * It inherits from JmlTestSuite the diagnostic collector implementation
 * and the (optional) collection of System.out and System.err.  It 
 * implements as well the mechanisms for running RAC via programmatic
 * calls to openjml and then executing the resulting program.
 * 
 * Tests may be based on files in the filesystem or on mock files.
 *
 */
public abstract class RacBase extends JmlTestSuite {

    // These are common strings for parts of expected output that can frequently change
    public static final String locA = "(Utils.java:143)";
    public static final String locB = "(Utils.java:94)";
    public static final String locC = "(Utils.java:96)";
    public static final String locD = "(Utils.java:127)";
    
    // These fields may be set by tests, in the test method itself, or after calling super.setUp
    protected int expectedExit = 0; // Expected result of compiler; may be set in a test
    protected int expectedRACExit = 0; // Expected result of RACed program; may be set in a test
    protected boolean continueAnyway = false; // If true, attempt to run the program despite compiler warnings or errors
    protected boolean runrac = true; // Only test compilation, not running the compiled file, if this field is false, or there is no executable name given, or the compile failed

    protected String testspecpath1 = "$A"+z+"$B";
    protected String testspecpath;

    /** File name of the expected output of compilation */
    protected String expected_compile = "expected-compile";
    /** File name of the expected output of running the RACed program */
    protected String expected_run = "expected-run";

    /** These are the default command-line arguments for running the RACed
     * program.  The first argument is the java executable; the null argument
     * is replaced by the class name of the class containing the main method.
     * */
    protected String[] defrac = new String[]{jdk, "-ea", "-classpath", "",null};

    /** These are actual command-line arguments, if they are set differently
     * by a subclass.
     */
    protected String[] rac = null; // initialized in subclasses

    /** Holds the path to the folder in which expected outputs are present and actual outputs are placed;
     * the path is relative to OpenJMLTest
     */
    protected String outdir;

    /** Derived classes can initialize
     * testspecpath1 - the specspath to use
     * <BR>jdkrac - default is false; if true, adjusts the classpath???
     * <BR>rac - the command-line to run the raced program; default is the contents of defrac
     * <BR>
     * After this call, if desired, modify
     * <BR>print - if true, prints out errors as encountered, for test debugging (and disables failing the JUnit test if the error mismatches)
     * <BR>expectedExit - the expected exit code from running openjml
     * <BR>expectedRacExit - the expected exit code from running the RACed program
     * <BR>expectedErrors - the expected number of errors from openjml (typically and by default 0)
     */
    @Override
    @Before
    public void setUp() throws Exception {
        //System.out.println("Using " + jdk);

        // Use the default specs path for tests
        testspecpath = testspecpath1;
        super.setUp();

        // Setup the options
        addOptions("--specs-path", testspecpath);
        //main.addJavaOption("-d", outdir); // This is where the output program goes // FIXME - for some reason this does not work here
        addOptions("--rac","--rac-java-checks","--rac-check-assumptions");
        addOptions("--show-not-implemented");
        addOptions("--rac-show-source=none"); // To make the test output more stable and smaller
        expectedExit = 0;
        expectedRACExit = 0;
        print = false;
    }

    @Override
    public void tearDown() throws Exception {
        super.tearDown();
    }

    public static String macstring = "Exception in thread \"main\" ";

    public String setupOutdir() {
        outdir = root + "/OpenJML/OpenJMLTest/testcompiles/" + getTestName();
        var d = new java.io.File(outdir);
        d.mkdirs();
        defrac[3] = outdir;
        if (rac == null) rac = new String[]{jdk, "-ea", "-classpath", outdir, null};
        return outdir;
    }

    /** This method does the running of a RAC test for tests that supply with body
     * of a file as a String.
     * No output is
     * expected from running openjml to produce the RACed program;
     * the number of expected diagnostics is set by 'expectedErrors'.
     * @param classname The fully-qualified classname for the test class
     * @param compilationUnitText the compilation unit text which will be put in a mock file
     * @param list any expected diagnostics from openjml, followed by the error messages from the RACed program, line by line
     */
    //public int expectedNotes = 0;
    //public void helpEsc(String classname, String compilationUnitText, Object... expectedDiagnostics) { helpRacText(classname, compilationUnitText, expectedDiagnostics); }

    public void helpRacText(String classname, String compilationUnitText, Object... expectedDiagnostics) {
        // Source files are synthetic
        // Compile destination is destdir
        // Expected output is contained in the test code (not in a file)
        String destdir = setupOutdir();
        new java.io.File(destdir).delete(); // Make sure old builds are deleted
        new java.io.File(destdir).mkdir();

        String term = "\n|(\r(\n)?)"; // any of the kinds of line terminators
        StreamGobbler outs=null,errs=null;
        boolean isMac = System.getProperty("os.name").contains("Mac");
        try {
            ListBuffer<JavaFileObject> files = new ListBuffer<JavaFileObject>();
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new MockJavaFileObject(filename,compilationUnitText);
            files.append(f);
            files.addAll(javamockFiles);

            Log.instance(context).useSource(files.first());

            int ex = main.compile(new String[]{"-d", destdir},files.toList()).exitCode;
            if (print) printDiagnostics();

            int expectedUsed = new OutputCompare().compareResults(expectedDiagnostics, collector, false);
            assertEquals("Compile ended with exit code:", expectedExit, ex);
            if (ex != 0 && !continueAnyway) return;
            if (!runrac) return;

            if (rac == null) rac = defrac;
            rac[rac.length-2] = destdir;
            rac[rac.length-1] = classname;
            Process p = Runtime.getRuntime().exec(rac);

            outs = new StreamGobbler(p.getInputStream());
            errs = new StreamGobbler(p.getErrorStream());
            outs.start();
            errs.start();
            if (timeout(p,10000)) { // 10 second timeout
                fail("Process did not complete within the timeout period");
            }

            int i = expectedUsed;
            if (print) {
                String data = outs.input();
                if (data.length() > 0) {
                    String[] lines = data.split(term);
                    for (String line: lines) {
                        out.println("OUT: " + line);
                    }
                }
                data = errs.input();
                if (data.length() > 0) {
                    String[] lines = data.split(term);
                    for (String line: lines) {
                        out.println("ERR: " + line);
                    }
                }
            }
            String data = outs.input();
            if (data.length() > 0) {
                String[] lines = data.split(term);
                for (String actual: lines) {
                    //out.println("ACT: " + line);
                    if (i < expectedDiagnostics.length) {
                        String expected = doReplacements(expectedDiagnostics[i].toString());
                        //out.println("EXP: " + expected);
                        if (expected.contains(":") && !actual.matches("^[^:]*:[0-9]+:.*")) 
                            expected = expected.replaceFirst("^[^:]*:[0-9]+: ","");
                        if (!actual.matches(".*:[0-9]+:$")) 
                            expected = expected.replaceFirst(": [^:]*:[0-9]+:$","");
                        //out.println("EXP: " + expected);
                        if (!expected.contains("verify: ")) actual = actual.replace("verify: ", "");
                        //out.println("EXP: " + expected);
                        assertEquals("Output line " + i, expected, actual);
                    }
                    i++;
                }
            }
            data = errs.input();
            if (data.length() > 0) {
                String[] lines = data.split(term);
                for (String actual: lines) {
                    //out.println("ERR-ACT: " + actual);
                    if (i < expectedDiagnostics.length) {
                        String expected = doReplacements(expectedDiagnostics[i].toString());
                        //out.println("ERR-EXP: " + expected);
                        if (actual.startsWith(macstring) && !expected.startsWith(macstring)) actual = actual.substring(macstring.length());
                        else if (!actual.startsWith(macstring) && expected.startsWith(macstring)) expected = expected.substring(macstring.length());
                        if (!expected.contains("verify: ")) actual = actual.replace("verify: ", "");
                        //out.println("ERR-EXP: " + expected);
                        assertEquals("Output line " + i, expected, actual);
                    }
                    i++;
                }
            }

            if (i != expectedDiagnostics.length && !print) { // if print, then we already printed
                printDiagnostics();
            }
            assertFalse("More output than specified: " + i + " vs. " + expectedDiagnostics.length + " lines", i > expectedDiagnostics.length);
            assertFalse("Less output than specified: " + i + " vs. " + expectedDiagnostics.length + " lines", i < expectedDiagnostics.length);
            if (p.exitValue() != expectedRACExit) fail("Exit code was " + p.exitValue());
        } catch (Exception e) {
            e.printStackTrace(this.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            if (!print) printDiagnostics();
            if (!print && !noExtraPrinting) {
                if (outs != null) {
                    String[] lines = outs.input().split(term);
                    for (String line: lines) {
                        out.println("OUT: " + line);
                    }
                }
                if (errs != null) {
                    String[] lines = errs.input().split(term);
                    for (String line: lines) {
                        out.println("ERR: " + line);
                    }
                }
            }
            throw e;
        }
    }

    /** Runs a test (RAC compilation only) on a test folder whose name is the same as the test name. */
    public void helpCompileOnly(String ... opts) {
        String dir = "test/" + getTestName();
        helpRac(dir, dir, null, opts);
    }

    /** Runs a test (RAC compilation and then running the compiled program) on a test folder whose name is the same as the test name. */
    public void helpCompileRun(String mainClassname, String ... opts) {
        String dir = "test/" + getTestName();
        helpRac(dir, dir, mainClassname, opts);
    }

    /** This method compiles a test with RAC whose source is in a given directory,
     * and then runs the compiled program.  The compilation is expected to have no errors.
     * the number of expected diagnostics is set by 'expectedErrors'.
     * 
     * 'sourcedir' is the directory containing the source files or the path to a single java file
     * 
     * The expected output files are contained in the given 'outputdir'
     * The working directory when the program is compiled and run is 'sourcedir' (or the containing directory if sourcedir is a file)
     * 
     * @param sourcedir The directory containing the test sources, a relative path
     * from the project folder
     * @param mainClassname The fully-qualified classname for the test class (where main is)
     */
 //   public void helpTCF(String sourcedir, String outputdir, String mainClassname, String ... opts) { helpRac(sourcedir, outputdir, mainClassname, opts); }
    public void helpRac(String sourcedir, String outputdir, String mainClassname, String ... opts) {
        String destDir = setupOutdir(); // This is the location for compiled .class files
        //        System.out.println("SOURCEDIR " + sourcedir);
        //        System.out.println("DESTDIR " + destDir);
        //        System.out.println("OUTDIR " + outputdir);
        //        System.out.println("OPTS " + String.join(",",opts));
        boolean print = false;
        StreamGobbler out=null,err=null;
        try {
            String actCompile = outputdir + "/actual-compile";
            String actRun = outputdir + "/actual-run";
            new File(outputdir).mkdirs();
            new File(actCompile).delete();
            new File(actRun).delete();
            List<String> args = new LinkedList<String>();
            args.add("-d");
            args.add(outdir); // Location of .class files
            //args.add("-classpath");
            //args.add(cp);
            args.add("--rac");
            args.add("--code-math=java");
            args.add("--spec-math=bigint");
            if (new File(sourcedir).isDirectory()) args.add("--dir");
            args.add(sourcedir);
            args.addAll(Arrays.asList(opts));

            PrintWriter pw = new PrintWriter(actCompile);
            int ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(String[]::new));
            pw.close();

            String compdiffs = "";
            boolean hasExpected = false;
            for (String file: new File(outputdir).list()) {
                if (!file.contains(expected_compile)) continue;
                hasExpected = true;
                compdiffs = outputCompare.compareFiles(outputdir + "/" + file, actCompile);
                if (compdiffs == null) {
                    new File(actCompile).delete();
                    break;
                }
            }
            if (compdiffs != null) {
                // No match found
                if (!hasExpected && java.nio.file.Files.readAllLines(java.nio.file.Paths.get(actCompile)).isEmpty()) {
                    // having no expected-compile file is equivalent to having an empty expected-compile file
                    new File(actCompile).delete();
                    compdiffs = null;
                } else if (compdiffs.isEmpty()) {
                    compdiffs = ("No expected output file for compiler output");
                    System.out.println(compdiffs);
                } else {
                    compdiffs = ("No match to actual file: " + compdiffs.substring(0, Math.min(150, compdiffs.length())));
                    System.out.println(compdiffs);
                    // Delay failing on file differences until after an attempt to run the file
                }
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex + " expected: " + expectedExit);

            if (runrac && ex == 0 && mainClassname != null) {
                if (rac == null) rac = defrac;
                rac[rac.length-1] = mainClassname;
                Process p = Runtime.getRuntime().exec(rac);

                out = new StreamGobbler(p.getInputStream());
                err = new StreamGobbler(p.getErrorStream());
                out.start();
                err.start();
                if (timeout(p,10000)) { // 10 second timeout
                    fail("Process did not complete within the timeout period");
                }
                String output = out.input().replaceAll("@[0-9abcdef]+", "@########");
                ex = p.exitValue();
                output = "OUT:" + eol + output + eol + "ERR:" + eol + err.input();
                if (print) this.out.println(output);
                String diffs = "";
                for (String file: new File(outputdir).list()) {
                    if (!file.contains(expected_run)) continue;
                    diffs = outputCompare.compareText(outputdir + "/" + file,output);
                    if (diffs == null) break;
                }
                if (diffs != null) {
                    BufferedWriter b = new BufferedWriter(new FileWriter(actRun));
                    b.write(output);
                    b.close();
                }
                if (ex != expectedRACExit) fail("Execution ended with exit code " + ex + " " + output);
                if (diffs != null) {
                    if (diffs.isEmpty()) {
                        fail("No expected output file for runtime output");
                    } else {
                        //this.out.println("EXP:" + outputdir + "   ACT: " + actRun + "   CUR: " + System.getProperty("user.dir") + "  DEMO: " + OpenJMLDemoPath);
                        if (print) this.out.println(diffs);
                        fail("Unexpected output: " + actRun);
                    }
                }
            } else {
                for (String file: new File(outputdir).list()) {
                    if (file.contains(expected_run)) {
                        fail("Test has an " + expected_run + " file even though the RACed program is not executed");
                    }
                }
            }
            if (compdiffs != null) {
                if (!print) compdiffs = actRun;
                fail("Files differ: " + compdiffs);
            }

        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            throw e;
        }
    }
}
