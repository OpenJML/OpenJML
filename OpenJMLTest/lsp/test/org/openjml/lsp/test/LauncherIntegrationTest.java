package org.openjml.lsp.test;

import org.junit.After;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.*;
import java.time.Duration;
import java.util.*;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Subprocess-based integration tests for the {@code openjml-lsp} launcher script.
 *
 * <p>All log-path logic (default path selection, {@code OPENJML_LSP_LOG} override,
 * stale-file cleanup, release-mode PID-qualified log creation) lives in the bash
 * launcher script, not in Java.  The existing in-process {@link LspProtocolTest}
 * infrastructure bypasses that script entirely, so these tests use
 * {@link ProcessBuilder} to spawn the real script and inspect the filesystem
 * afterward.
 *
 * <h3>Preconditions</h3>
 * <ul>
 *   <li>System property {@code lsp.testdata} must be set (done by the Makefile).</li>
 *   <li>{@code openjml-lsp.jar} and the LSP4J jars must already be built
 *       ({@code make jar} in {@code OpenJMLlsp/}).</li>
 * </ul>
 *
 * <h3>Release-mode simulation</h3>
 * {@link #testStaleLogCleanup()} and {@link #testReleaseModeLogFileCreated()}
 * need the script to take the release code path (triggered by a {@code jdk/}
 * directory present next to the script).  The test constructs a self-contained
 * temporary installation directory containing a copy of the script and symlinks
 * to the real built JDK, {@code setup-exports}, server jar, and LSP4J libraries.
 * No permanent changes are made to the repository tree.
 */
public class LauncherIntegrationTest {

    /** Seconds to wait for the server to respond to {@code initialize}. */
    private static final int HANDSHAKE_TIMEOUT_SEC = 30;

    /** Seconds to wait for the process to exit after {@code exit}. */
    private static final int EXIT_TIMEOUT_SEC = 15;

    private static final String LSP4J_VERSION = "1.0.0";

    /** Root of the {@code OpenJMLlsp} module (resolved from {@code lsp.testdata}). */
    private static final Path LSP_ROOT;

    /** Root of the {@code OpenJMLsrc} module (sibling of {@code OpenJMLlsp}). */
    private static final Path SRC_ROOT;

    /** The {@code openjml-lsp} launcher script. */
    private static final Path LAUNCHER_SCRIPT;

    static {
        String testdata = System.getProperty("lsp.testdata");
        if (testdata != null) {
            // lsp.testdata = .../OpenJMLTest/lsp/testdata
            Path td = Paths.get(testdata);
            LSP_ROOT        = td.getParent().getParent().getParent().resolve("OpenJMLlsp");
            SRC_ROOT        = LSP_ROOT.getParent().resolve("OpenJMLsrc");
            LAUNCHER_SCRIPT = LSP_ROOT.resolve("openjml-lsp");
        } else {
            LSP_ROOT        = null;
            SRC_ROOT        = null;
            LAUNCHER_SCRIPT = null;
        }
    }

    /** Processes spawned during a test — forcibly killed in {@link #tearDown()}. */
    private final List<Process> processes = new ArrayList<>();

    /** Temp directories created during a test — deleted recursively in {@link #tearDown()}. */
    private final List<Path> tempDirs = new ArrayList<>();

    @Before
    public void checkPrerequisites() {
        assertNotNull("System property lsp.testdata must be set", LSP_ROOT);
        assertTrue("openjml-lsp script must exist: " + LAUNCHER_SCRIPT,
                LAUNCHER_SCRIPT != null && Files.exists(LAUNCHER_SCRIPT));
        assertTrue("openjml-lsp.jar must be built (run 'make jar' in OpenJMLlsp/): "
                        + LSP_ROOT.resolve("build/openjml-lsp.jar"),
                Files.exists(LSP_ROOT.resolve("build/openjml-lsp.jar")));
    }

    @After
    public void tearDown() {
        for (Process p : processes) {
            if (p.isAlive()) p.destroyForcibly();
        }
        for (Path dir : tempDirs) {
            deleteRecursive(dir);
        }
    }

    // -----------------------------------------------------------------------
    // Test 1: OPENJML_LSP_LOG override is honored (dev mode)
    // -----------------------------------------------------------------------

    /**
     * Verifies that setting {@code OPENJML_LSP_LOG} to an explicit path causes
     * the server to write its log there instead of the default
     * {@code /tmp/openjml-lsp-debug.log}.
     */
    @Test
    public void testLogOverrideHonored() throws Exception {
        Path customLog = Files.createTempFile("openjml-lsp-override-test-", ".log");
        customLog.toFile().deleteOnExit();

        Process proc = spawnScript(LAUNCHER_SCRIPT,
                Map.of("OPENJML_LSP_LOG", customLog.toAbsolutePath().toString()));
        doHandshakeAndShutdown(proc);

        assertTrue("OPENJML_LSP_LOG override path must exist after server run: " + customLog,
                Files.exists(customLog));
        assertTrue("Log file at OPENJML_LSP_LOG override path must be non-empty",
                Files.size(customLog) > 0);
    }

    // -----------------------------------------------------------------------
    // Test 2: Stale log cleanup on startup (release mode)
    // -----------------------------------------------------------------------

    /**
     * Verifies that the server deletes stale log files (dead-process PID, older
     * than one day) from {@code ~/.openjml/logs/} on startup, while leaving log
     * files for still-running processes untouched.
     *
     * <p>The test controls {@code HOME} via the subprocess environment so that
     * the log directory is a temporary directory under our control.  A log for
     * PID&nbsp;99999 (assumed not running) with a two-day-old mtime is the stale
     * candidate.  A log for the current JVM's PID (definitely running) with the
     * same old mtime is the live candidate that must survive.
     */
    @Test
    public void testStaleLogCleanup() throws Exception {
        // If PID 99999 happens to be alive on this machine the test cannot run.
        Assume.assumeFalse(
                "PID 99999 is currently running; cannot use it as a dead-PID test fixture",
                ProcessHandle.of(99999L).isPresent());

        Path tmpHome = createTempDir("openjml-test-home-");
        Path logDir  = tmpHome.resolve(".openjml/logs");
        Files.createDirectories(logDir);

        // Stale log: dead PID, mtime 2 days ago — must be deleted.
        Path staleLog = logDir.resolve("openjml-lsp-99999.log");
        Files.writeString(staleLog, "stale");
        staleLog.toFile().setLastModified(
                System.currentTimeMillis() - Duration.ofDays(2).toMillis());

        // Live log: current JVM's PID, same old mtime — must survive because
        // the process is running and kill -0 succeeds for it.
        long livePid = ProcessHandle.current().pid();
        Path liveLog = logDir.resolve("openjml-lsp-" + livePid + ".log");
        Files.writeString(liveLog, "live");
        liveLog.toFile().setLastModified(
                System.currentTimeMillis() - Duration.ofDays(2).toMillis());

        // Route our instance's log to a temp file so it does not land in the
        // controlled logDir (which would interfere with the stale-file assertions).
        Path ownLog = Files.createTempFile(logDir, "openjml-lsp-test-own-", ".log");

        Path install = createReleaseInstall();
        Path script  = install.resolve("openjml-lsp");

        // The stale-log cleanup runs before `exec java`, so even if the server
        // exits early the cleanup has already happened.
        Process proc = spawnScript(script, Map.of(
                "HOME",            tmpHome.toAbsolutePath().toString(),
                "OPENJML_LSP_LOG", ownLog.toAbsolutePath().toString()));
        proc.waitFor(EXIT_TIMEOUT_SEC, TimeUnit.SECONDS);
        if (proc.isAlive()) proc.destroyForcibly();

        assertFalse("Stale log for dead PID 99999 must be deleted by server startup",
                Files.exists(staleLog));
        assertTrue("Log for live PID " + livePid + " must survive (process is running)",
                Files.exists(liveLog));
    }

    // -----------------------------------------------------------------------
    // Test 3: PID-qualified log file is created in release mode
    // -----------------------------------------------------------------------

    /**
     * Verifies that the server creates a PID-qualified log file at
     * {@code ~/.openjml/logs/openjml-lsp-<pid>.log} when running in release
     * mode (a {@code jdk/} directory present next to the launcher script), and
     * that the file is non-empty.
     *
     * <p>The process PID is obtained from {@link Process#pid()} immediately
     * after {@link ProcessBuilder#start()}.  Because the bash script uses
     * {@code exec java …} to replace itself in-place, the PID of the bash process
     * ({@code $$}) equals the PID of the eventual Java server process, so
     * {@code process.pid()} matches the filename that the script writes.
     */
    @Test
    public void testReleaseModeLogFileCreated() throws Exception {
        Path tmpHome = createTempDir("openjml-test-home-");
        Path install = createReleaseInstall();
        Path script  = install.resolve("openjml-lsp");

        Process proc = spawnScript(script, Map.of(
                "HOME",            tmpHome.toAbsolutePath().toString(),
                "OPENJML_INSTALL", install.toAbsolutePath().toString()));
        long pid = proc.pid();

        doHandshakeAndShutdown(proc);

        Path expectedLog = tmpHome.resolve(".openjml/logs/openjml-lsp-" + pid + ".log");
        assertTrue("Release-mode PID-qualified log must exist at: " + expectedLog,
                Files.exists(expectedLog));
        assertTrue("Release-mode log must be non-empty",
                Files.size(expectedLog) > 0);
    }

    // -----------------------------------------------------------------------
    // Infrastructure helpers
    // -----------------------------------------------------------------------

    /**
     * Spawn the given launcher script as a subprocess.  The environment is
     * inherited from the current process and then {@code envOverrides} are
     * applied on top.  The process's stderr is discarded (the script redirects
     * its own stderr to the log file; any pre-redirect errors are immaterial
     * here).  The spawned process is registered for cleanup in {@link #tearDown()}.
     */
    private Process spawnScript(Path script, Map<String, String> envOverrides)
            throws IOException {
        ProcessBuilder pb = new ProcessBuilder(script.toAbsolutePath().toString());
        pb.environment().putAll(envOverrides);
        pb.redirectError(ProcessBuilder.Redirect.DISCARD);
        Process proc = pb.start();
        processes.add(proc);
        return proc;
    }

    /**
     * Perform the minimal LSP handshake — {@code initialize} / {@code initialized}
     * / {@code shutdown} / {@code exit} — then wait for the process to exit.
     *
     * <p>The LSP wire must be actively consumed or the Java process will block
     * once its stdout pipe buffer fills.
     */
    private void doHandshakeAndShutdown(Process proc) throws Exception {
        RawLspClient client = new RawLspClient(proc.getOutputStream(), proc.getInputStream());
        try {
            client.sendRequest("initialize",
                    "{\"processId\":" + proc.pid()
                    + ",\"rootUri\":null,\"capabilities\":{}}");
            var response = client.nextResponse(HANDSHAKE_TIMEOUT_SEC, TimeUnit.SECONDS);
            assertNotNull(
                    "Server must respond to initialize within " + HANDSHAKE_TIMEOUT_SEC + " s",
                    response);
            client.sendNotification("initialized", "{}");
            client.sendRequest("shutdown", null);
            client.nextResponse(10, TimeUnit.SECONDS);
            client.sendNotification("exit", null);
        } finally {
            client.stop();
        }
        boolean exited = proc.waitFor(EXIT_TIMEOUT_SEC, TimeUnit.SECONDS);
        if (!exited) proc.destroyForcibly();
    }

    /**
     * Build a self-contained temporary release-layout installation directory.
     *
     * <p>The directory contains:
     * <ul>
     *   <li>a copy of the {@code openjml-lsp} script (its parent dir becomes
     *       {@code $DIR} in the script, making relative-path detection work),</li>
     *   <li>{@code jdk/} — symlink to the real built JDK; its presence triggers
     *       the release-mode branch in the script,</li>
     *   <li>{@code setup-exports} — symlink to the real file in {@code OpenJMLsrc/},</li>
     *   <li>{@code lsp/openjml-lsp.jar} and the two LSP4J jars — symlinks to
     *       the real built artifacts in {@code OpenJMLlsp/}.</li>
     * </ul>
     *
     * <p>The directory is registered for deletion in {@link #tearDown()}.
     */
    private Path createReleaseInstall() throws IOException {
        Path install = createTempDir("openjml-fake-release-");

        // Copy the launcher script so its parent ($DIR) is our install root.
        Path script = install.resolve("openjml-lsp");
        Files.copy(LAUNCHER_SCRIPT, script);
        script.toFile().setExecutable(true);

        // jdk/ symlink — its existence flips the script into release mode.
        Path builtJdk = resolveBuiltJdk();
        Files.createSymbolicLink(install.resolve("jdk"), builtJdk);

        // setup-exports — sourced by the script during release-mode Java setup.
        Files.createSymbolicLink(
                install.resolve("setup-exports"),
                SRC_ROOT.resolve("setup-exports").toAbsolutePath());

        // lsp/ directory with the server jar and LSP4J libraries.
        Path lspDir = install.resolve("lsp");
        Files.createDirectories(lspDir);
        Files.createSymbolicLink(
                lspDir.resolve("openjml-lsp.jar"),
                LSP_ROOT.resolve("build/openjml-lsp.jar").toAbsolutePath());
        for (String jar : List.of(
                "org.eclipse.lsp4j-" + LSP4J_VERSION + ".jar",
                "org.eclipse.lsp4j.jsonrpc-" + LSP4J_VERSION + ".jar")) {
            Files.createSymbolicLink(
                    lspDir.resolve(jar),
                    LSP_ROOT.resolve("libs/" + jar).toAbsolutePath());
        }

        return install;
    }

    /**
     * Locate the built JDK directory.
     *
     * <p>The Makefile passes {@code OPENJML_INSTALL="$(BUILDJDK)"} to test
     * processes, so the environment variable points directly at the built JDK
     * (e.g. {@code OpenJMLsrc/build/macosx-x86_64-server-release/jdk}).  If the
     * variable is absent or stale, a glob fallback scans {@code OpenJMLsrc/build/}.
     */
    private static Path resolveBuiltJdk() {
        String envInstall = System.getenv("OPENJML_INSTALL");
        if (envInstall != null) {
            Path p = Paths.get(envInstall);
            if (Files.isDirectory(p) && Files.exists(p.resolve("bin/java"))) {
                return p.toAbsolutePath();
            }
        }
        // Fallback: glob for the jdk directory under OpenJMLsrc/build/
        try (DirectoryStream<Path> builds =
                Files.newDirectoryStream(SRC_ROOT.resolve("build"))) {
            for (Path entry : builds) {
                Path jdk = entry.resolve("jdk");
                if (Files.isDirectory(jdk) && Files.exists(jdk.resolve("bin/java"))) {
                    return jdk.toAbsolutePath();
                }
            }
        } catch (IOException ignored) {}
        throw new IllegalStateException(
                "Cannot locate the built JDK.  Set OPENJML_INSTALL to the jdk/ directory "
                + "or run 'make openjml' in OpenJMLsrc/ first.");
    }

    private Path createTempDir(String prefix) throws IOException {
        Path dir = Files.createTempDirectory(prefix);
        tempDirs.add(dir);
        return dir;
    }

    /** Recursively delete {@code path} (best-effort; ignores individual errors). */
    private static void deleteRecursive(Path path) {
        if (path == null || !Files.exists(path)) return;
        try (var walk = Files.walk(path)) {
            walk.sorted(Comparator.reverseOrder())
                .forEach(p -> { try { Files.deleteIfExists(p); } catch (IOException ignored) {} });
        } catch (IOException ignored) {}
    }
}
