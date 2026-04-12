package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.OpenJMLCommands;
import org.openjml.lsp.OpenJMLLanguageServer;

import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for per-project settings configured via
 * {@code workspace/didChangeConfiguration}.
 *
 * <p>Each test starts a fresh in-process LSP server so server state does not
 * leak between tests.  A temporary directory is created per test and torn down
 * in {@code @After}.
 *
 * <h3>Coverage targets</h3>
 * <ul>
 *   <li>{@link #testProjectConfigurationApplied} — {@code didChangeConfiguration}
 *       with a {@code projects} list registers project settings; a subsequent
 *       {@code openjml.checkJML} on a file in the configured root publishes
 *       diagnostics using those settings.</li>
 *   <li>{@link #testCheckJmlForTwoProjects} — two projects can be configured
 *       simultaneously; {@code openjml.checkJML} on a file in each project
 *       publishes separate diagnostics notifications.  The two commands are
 *       sent sequentially (the first check completes before the second is
 *       issued) so that the 300 ms {@code scheduleCheckForPaths} debounce
 *       fires independently for each one.</li>
 *   <li>{@link #testFocusFileSkipsUntrackedUri} — when projects are configured,
 *       {@code openjml.focusFile} for a URI that does not match any project's
 *       {@code rootPaths} is silently skipped ({@code recheckUri} returns early
 *       because {@code settingsForUri(uri) == settings}), and no
 *       {@code textDocument/publishDiagnostics} is published for that URI.</li>
 * </ul>
 */
public class MultiProjectTest {

    private static final long TIMEOUT_SECONDS = 120;
    private static final long SHORT_TIMEOUT   = 5;

    private OpenJMLLanguageServer server;
    private RawLspClient          client;
    private Path                  tmpDir;

    // -----------------------------------------------------------------------
    // Per-test server and temp-file lifecycle
    // -----------------------------------------------------------------------

    @Before
    public void setUp() throws Exception {
        tmpDir = Files.createTempDirectory("MultiProjectTest-");
        createTestFiles();

        PipedInputStream  serverIn  = new PipedInputStream(65536);
        PipedOutputStream clientOut = new PipedOutputStream(serverIn);
        PipedInputStream  clientIn  = new PipedInputStream(65536);
        PipedOutputStream serverOut = new PipedOutputStream(clientIn);

        server = new OpenJMLLanguageServer();
        var launcher = LSPLauncher.createServerLauncher(server, serverIn, serverOut);
        server.connect(launcher.getRemoteProxy());
        launcher.startListening();

        client = new RawLspClient(clientOut, clientIn);
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,\"capabilities\":{}}");
        assertNotNull("Server must respond to initialize",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
        client.sendNotification("initialized", "{}");
    }

    @After
    public void tearDown() throws Exception {
        if (client != null) client.stop();
        if (tmpDir != null && Files.exists(tmpDir)) {
            Files.walk(tmpDir)
                    .sorted(Comparator.reverseOrder())
                    .forEach(p -> p.toFile().delete());
        }
    }

    private void createTestFiles() throws Exception {
        // Java file with a type error — used to verify checkJML ran and produced diags.
        write("ProjectA", "ProjAError.java",
                "public class ProjAError {\n"
                + "    public int m() { return \"not an int\"; }\n"
                + "}\n");

        // Clean Java file in a distinct subdirectory — used for the two-project test.
        write("ProjectB", "ProjBClean.java",
                "public class ProjBClean {\n"
                + "    public void hello() { System.out.println(\"hello\"); }\n"
                + "}\n");
    }

    private void write(String subdir, String name, String content) throws Exception {
        Path dir = tmpDir.resolve(subdir);
        Files.createDirectories(dir);
        Files.writeString(dir.resolve(name), content, StandardCharsets.UTF_8);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private String absPath(String subdir, String name) {
        return tmpDir.resolve(subdir).resolve(name).toAbsolutePath().toString();
    }

    private String absDir(String subdir) {
        return tmpDir.resolve(subdir).toAbsolutePath().toString();
    }

    private static String jsonEscapePath(String path) {
        return path.replace("\\", "\\\\");
    }

    private static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    /**
     * Register one project via {@code workspace/didChangeConfiguration}.
     */
    private void configureOneProject(String projectId, String rootPath) throws Exception {
        String root = jsonEscapePath(rootPath);
        String settingsJson = "{\"openjml\":{\"projects\":[{\"id\":\"" + projectId
                + "\",\"rootPaths\":[\"" + root + "\"]}]}}";
        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":" + settingsJson + "}");
        // Brief pause to let the server apply the configuration synchronously.
        Thread.sleep(100);
    }

    /**
     * Register two projects via {@code workspace/didChangeConfiguration}.
     */
    private void configureTwoProjects(
            String idA, String rootA, String idB, String rootB) throws Exception {
        String rA = jsonEscapePath(rootA);
        String rB = jsonEscapePath(rootB);
        String settingsJson = "{\"openjml\":{\"projects\":["
                + "{\"id\":\"" + idA + "\",\"rootPaths\":[\"" + rA + "\"]},"
                + "{\"id\":\"" + idB + "\",\"rootPaths\":[\"" + rB + "\"]}"
                + "]}}";
        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":" + settingsJson + "}");
        Thread.sleep(100);
    }

    /**
     * Send an {@code openjml.checkJML} command using the old VS Code 4-element-prefix
     * format and drain the immediate null response.
     */
    private void sendCheckJml(String osPath) throws Exception {
        String escaped = jsonEscapePath(osPath);
        String params = "{\"command\":\"" + OpenJMLCommands.CHECK_JML
                + "\",\"arguments\":[\"\",\"\",\"\",\"\",\"" + escaped + "\"]}";
        client.sendRequest("workspace/executeCommand", params);
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    private JsonObject nextDiagsFor(String fragment, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            if (msg.getAsJsonObject("params").get("uri").getAsString().contains(fragment))
                return msg;
        }
    }

    // -----------------------------------------------------------------------
    // Test 1: single project configuration applied to checkJML
    // -----------------------------------------------------------------------

    /**
     * Configure a single project whose {@code rootPaths} includes
     * {@code tmpDir/ProjectA}.  Send {@code openjml.checkJML} for a file with a
     * type error in that directory; verify that a non-empty
     * {@code textDocument/publishDiagnostics} is received, confirming the check ran.
     *
     * <p>Exercises {@code updateProjectSettings} → {@code projectSettings} map
     * populated → {@code scheduleCheckForPaths} with project-specific settings.
     */
    @Test
    public void testProjectConfigurationApplied() throws Exception {
        configureOneProject("projA", absDir("ProjectA"));

        sendCheckJml(absPath("ProjectA", "ProjAError.java"));

        JsonObject note = nextDiagsFor("ProjAError", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after checkJML on project-A file", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("File with type error in configured project must produce diagnostics",
                diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Test 2: two projects configured simultaneously
    // -----------------------------------------------------------------------

    /**
     * Configure two projects (A and B) simultaneously.  Run
     * {@code openjml.checkJML} on a file from project A, wait for its
     * diagnostics, then run {@code openjml.checkJML} on a file from project B.
     *
     * <p>Sending the commands sequentially (rather than back-to-back) prevents
     * the second command from cancelling the first's 300 ms
     * {@code scheduleCheckForPaths} debounce.  Both files must receive their
     * own {@code textDocument/publishDiagnostics} notification.
     *
     * <p>Exercises the per-project settings registry ({@code projectSettings} map)
     * with two entries and independent debounce scheduling per command.
     */
    @Test
    public void testCheckJmlForTwoProjects() throws Exception {
        configureTwoProjects("projA", absDir("ProjectA"),
                             "projB", absDir("ProjectB"));

        // Send checkJML for project A and wait for its diagnostics before sending B.
        // The scheduleCheckForPaths debounce is shared (pendingCheckPaths), so sending
        // both commands back-to-back would cancel A's debounce and only check B.
        sendCheckJml(absPath("ProjectA", "ProjAError.java"));
        JsonObject noteA = nextDiagsFor("ProjAError", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics for project-A file", noteA);
        JsonArray diagsA = noteA.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("File with type error in project A must produce diagnostics", diagsA.isEmpty());

        // Now send checkJML for project B.
        sendCheckJml(absPath("ProjectB", "ProjBClean.java"));
        JsonObject noteB = nextDiagsFor("ProjBClean", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics for project-B file", noteB);
        JsonArray diagsB = noteB.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("Clean project-B file must produce empty diagnostics", diagsB.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Tests: commands with an unrecognized project ID
    // -----------------------------------------------------------------------

    /**
     * Sends {@code openjml.checkJML} with an args[0] that looks syntactically like
     * a project ID (no path characters) but is not in the project registry.
     *
     * <p>{@code isNewFormat()} calls {@code isKnownProject(args[0])}, which returns
     * {@code false} for an unrecognized ID, so the command degrades to old-format and
     * {@code cmdProject()} returns {@code null}.  The server must not crash, must return
     * a response, and must still be responsive to a subsequent request.
     */
    @Test
    public void testCheckJmlWithUnknownProjectIdGracefulDegradation() throws Exception {
        configureOneProject("projA", absDir("ProjectA"));

        // Send checkJML with an unregistered project ID in args[0].
        String params = "{\"command\":\"" + OpenJMLCommands.CHECK_JML
                + "\",\"arguments\":[\"unknownProject\",\""
                + jsonEscapePath(absPath("ProjectA", "ProjAError.java")) + "\"]}";
        client.sendRequest("workspace/executeCommand", params);
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to checkJML with unknown project ID", resp);

        // Server must still be responsive.
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.CLEAR_AND_REINDEX + "\",\"arguments\":[]}");
        assertNotNull("Server must respond to subsequent command after unknown-project checkJML",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
    }

    /**
     * Sends {@code openjml.indexProject} with an unrecognized project ID.
     *
     * <p>Same degradation as {@link #testCheckJmlWithUnknownProjectIdGracefulDegradation}:
     * {@code isNewFormat()} returns {@code false}, so {@code cmdProject()} returns
     * {@code null} and {@code indexProject(null)} indexes all configured projects.
     * The server must respond without error and remain responsive.
     */
    @Test
    public void testIndexProjectWithUnknownProjectIdGracefulDegradation() throws Exception {
        configureOneProject("projA", absDir("ProjectA"));

        String params = "{\"command\":\"" + OpenJMLCommands.INDEX_PROJECT
                + "\",\"arguments\":[\"noSuchProject\"]}";
        client.sendRequest("workspace/executeCommand", params);
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to indexProject with unknown project ID", resp);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.CLEAR_AND_REINDEX + "\",\"arguments\":[]}");
        assertNotNull("Server must remain responsive after unknown-project indexProject",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
    }

    /**
     * Sends {@code openjml.runEsc} with an unrecognized project ID.  Verifies the
     * server responds and remains responsive (does not crash or block).
     */
    @Test
    public void testRunEscWithUnknownProjectIdGracefulDegradation() throws Exception {
        configureOneProject("projA", absDir("ProjectA"));

        String params = "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"ghostProject\",\""
                + jsonEscapePath(absPath("ProjectA", "ProjAError.java")) + "\"]}";
        client.sendRequest("workspace/executeCommand", params);
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to runEsc with unknown project ID", resp);

        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.CLEAR_AND_REINDEX + "\",\"arguments\":[]}");
        assertNotNull("Server must remain responsive after unknown-project runEsc",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
    }

    // -----------------------------------------------------------------------
    // Test 3: focusFile no-op for URI outside all project roots
    // -----------------------------------------------------------------------

    /**
     * When projects are configured, both {@code scheduleCheckNow} and
     * {@code recheckUri} skip files whose URI does not match any project's
     * {@code rootPaths} (the guard {@code settingsForUri(uri) == null} fires).
     *
     * <p>Sequence:
     * <ol>
     *   <li>Configure one project rooted at {@code tmpDir/ProjectA}.</li>
     *   <li>Open {@code file:///UntrackedFocus.java} (not under
     *       {@code tmpDir/ProjectA}) — {@code scheduleCheckNow} returns early;
     *       no {@code textDocument/publishDiagnostics} is published.</li>
     *   <li>Send {@code openjml.focusFile} for the untracked URI —
     *       {@code recheckUri} returns early due to the same guard.</li>
     *   <li>Assert no {@code textDocument/publishDiagnostics} arrives for the
     *       untracked URI within a short window.</li>
     *   <li>Assert the server is still responsive.</li>
     * </ol>
     */
    @Test
    public void testFocusFileSkipsUntrackedUri() throws Exception {
        configureOneProject("projFocus", absDir("ProjectA"));

        // Open the untracked file.  scheduleCheckNow returns early (project guard),
        // so NO publishDiagnostics is expected from this didOpen.
        String uri = "file:///UntrackedFocus.java";
        String source = "public class UntrackedFocus { public int x = 1; }\n";
        String openParams = "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}";
        client.sendNotification("textDocument/didOpen", openParams);

        // Allow the (skipped) debounce window to pass so there are no latent checks.
        Thread.sleep(700);

        // Send focusFile.  recheckUri checks lastContent (has the file) and then the
        // project guard (settingsForUri == null for a URI outside all roots) — returns early.
        String focusParams = "{\"command\":\"" + OpenJMLCommands.FOCUS_FILE
                + "\",\"arguments\":[\"" + uri + "\"]}";
        client.sendRequest("workspace/executeCommand", focusParams);
        JsonObject focusResp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to focusFile command", focusResp);

        // No publishDiagnostics should arrive for the untracked URI within 2 seconds.
        JsonObject diags = nextDiagsFor("UntrackedFocus", 2, TimeUnit.SECONDS);
        assertNull("recheckUri must be a no-op for a URI outside all configured project roots",
                diags);

        // The server must still be responsive after the no-op.
        client.sendRequest("textDocument/codeLens",
                "{\"textDocument\":{\"uri\":\"" + uri + "\"}}");
        assertNotNull("Server must respond to codeLens after no-op focusFile",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
    }
}
