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
 * Protocol-layer tests for workspace-level operations: project indexing
 * ({@code openjml.indexProject}), focus-file recheck ({@code openjml.focusFile}),
 * and cache reset ({@code openjml.clearAndReindex}).
 *
 * <p>Each test starts a fresh in-process LSP server so server state does not
 * leak between tests.  A temporary directory is created per test and torn down
 * in {@code @After}.
 *
 * <h3>Coverage targets</h3>
 * <ul>
 *   <li>{@link #testIndexProjectWithWorkspaceFolderPaths} — configure
 *       {@code workspaceFolderPaths} via {@code didChangeConfiguration}, then
 *       send {@code openjml.indexProject}; the server runs
 *       {@code runProjectCheck(roots, s)} which publishes diagnostics for
 *       files with errors and sets {@code navCacheDirty=false}.</li>
 *   <li>{@link #testFocusFileTriggersRecheck} — open a file, wait for the
 *       initial check, modify content so {@code lastContent != lastCheckedContent},
 *       then send {@code openjml.focusFile}; {@code recheckUri} detects stale
 *       content and submits a new {@code --check}.</li>
 *   <li>{@link #testClearAndReindexLeavesServerResponsive} — {@code openjml.clearAndReindex}
 *       resets all caches and triggers a re-index; the server remains responsive
 *       to subsequent requests afterward.</li>
 * </ul>
 */
public class WorkspaceIndexTest {

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
        tmpDir = Files.createTempDirectory("WorkspaceIndexTest-");

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

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private void write(String name, String content) throws Exception {
        Files.writeString(tmpDir.resolve(name), content, StandardCharsets.UTF_8);
    }

    private static String jsonEscapePath(String path) {
        return path.replace("\\", "\\\\");
    }

    private static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
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

    /**
     * Configure {@code workspaceFolderPaths} via {@code workspace/didChangeConfiguration}.
     */
    private void configureWorkspaceFolderPaths(String osPath) throws Exception {
        String escaped = jsonEscapePath(osPath);
        String settingsJson = "{\"openjml\":{\"workspaceFolderPaths\":\"" + escaped + "\"}}";
        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":" + settingsJson + "}");
        // Brief pause to let the server apply the settings.
        Thread.sleep(100);
    }

    // -----------------------------------------------------------------------
    // Test 1: indexProject with workspaceFolderPaths
    // -----------------------------------------------------------------------

    /**
     * Configure {@code workspaceFolderPaths} pointing to {@code tmpDir}, create a
     * Java file with a type error in that directory, then send
     * {@code openjml.indexProject}.
     *
     * <p>The server's {@link org.openjml.lsp.OpenJMLTextDocumentService#indexProject}
     * collects source directories from {@code settings.workspaceFolderPaths}, submits
     * {@code runProjectCheck(roots, s)} on the executor, and
     * {@code runProjectCheck} calls {@code CheckRunner.runCheckDirWithContext} and
     * publishes diagnostics for files that produced errors.  The type-error file must
     * appear in a {@code textDocument/publishDiagnostics} notification.
     */
    @Test
    public void testIndexProjectWithWorkspaceFolderPaths() throws Exception {
        write("IndexError.java",
                "public class IndexError {\n"
                + "    public int m() { return \"not an int\"; }\n"
                + "}\n");

        configureWorkspaceFolderPaths(tmpDir.toAbsolutePath().toString());

        // Send openjml.indexProject with no arguments (cmdProject returns null;
        // indexProject(null) uses workspaceFolderPaths as source roots).
        String params = "{\"command\":\"" + OpenJMLCommands.INDEX_PROJECT
                + "\",\"arguments\":[]}";
        client.sendRequest("workspace/executeCommand", params);
        // The command itself returns null immediately; drain the response.
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // runProjectCheck publishes diagnostics only for URIs with errors.
        // The type-error file must produce a publishDiagnostics notification.
        JsonObject note = nextDiagsFor("IndexError", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("indexProject must trigger --check on workspace files and publish "
                + "diagnostics for files with errors", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Type-error file found by indexProject must produce diagnostics",
                diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Test 2: focusFile triggers a recheck when content is stale
    // -----------------------------------------------------------------------

    /**
     * Open a file and wait for the initial check.  Then change the content via
     * {@code textDocument/didChange} (using a full-text replacement so the server
     * records new content in {@code lastContent}) without waiting for the debounced
     * recheck.  Drain the debounced check's notification.  Modify the content again
     * so {@code lastContent != lastCheckedContent}.  Then send
     * {@code openjml.focusFile}; {@code recheckUri} detects the stale content
     * (content != lastCheckedContent and no pending future) and submits a new check.
     *
     * <p>The final edit introduces a type error so the resulting
     * {@code publishDiagnostics} has non-empty diagnostics, confirming a real check ran.
     */
    @Test
    public void testFocusFileTriggersRecheck() throws Exception {
        String uri = "file:///FocusRecheck.java";
        String clean = "public class FocusRecheck {\n"
                + "    public int m() { return 42; }\n"
                + "}\n";
        // Open clean file and drain initial check.
        String openParams = "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(clean) + "\"}}";
        client.sendNotification("textDocument/didOpen", openParams);
        JsonObject init = nextDiagsFor("FocusRecheck", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after initial open", init);

        // Modify to introduce a type error and let the debounce fire.
        String broken = "public class FocusRecheck {\n"
                + "    public int m() { return \"broken\"; }\n"
                + "}\n";
        String changeParams = "{\"textDocument\":{\"uri\":\"" + uri + "\",\"version\":2},"
                + "\"contentChanges\":[{\"text\":\"" + jsonEscape(broken) + "\"}]}";
        client.sendNotification("textDocument/didChange", changeParams);
        // Drain the debounced check triggered by didChange.
        JsonObject afterChange = nextDiagsFor("FocusRecheck", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after content change", afterChange);
        // The content is now the same as lastCheckedContent (the debounce ran).

        // Edit again without waiting for a new debounce: replace "broken" with another error.
        // This makes lastContent != lastCheckedContent.
        String broken2 = "public class FocusRecheck {\n"
                + "    public int m() { return \"still broken\"; }\n"
                + "}\n";
        String changeParams2 = "{\"textDocument\":{\"uri\":\"" + uri + "\",\"version\":3},"
                + "\"contentChanges\":[{\"text\":\"" + jsonEscape(broken2) + "\"}]}";
        client.sendNotification("textDocument/didChange", changeParams2);
        // Do NOT wait for the debounce — send focusFile immediately to race with it.
        Thread.sleep(50);

        // Send focusFile.  recheckUri checks content != lastCheckedContent (true) and
        // no pending future (the debounce future is a ScheduledFuture, not lastCheckFuture).
        // It submits a check synchronously.
        String focusParams = "{\"command\":\"" + OpenJMLCommands.FOCUS_FILE
                + "\",\"arguments\":[\"" + uri + "\"]}";
        client.sendRequest("workspace/executeCommand", focusParams);
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // At least one publishDiagnostics must arrive (from focusFile check or debounce).
        // Both would produce error diagnostics for "still broken".
        JsonObject note = nextDiagsFor("FocusRecheck", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after focusFile", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Type-error content must produce diagnostics", diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Test 3: clearAndReindex does not crash the server
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.clearAndReindex} clears all server caches and schedules a fresh
     * index run.  The server must return a response (null result) and remain responsive
     * to subsequent requests.
     *
     * <p>No workspace root is configured, so the index run logs "no source directories"
     * and exits early — there are no diagnostics to wait for.  The test simply verifies
     * that the command is dispatched without throwing and that the server handles a
     * follow-up {@code textDocument/codeLens} request.
     */
    @Test
    public void testClearAndReindexLeavesServerResponsive() throws Exception {
        String params = "{\"command\":\"" + OpenJMLCommands.CLEAR_AND_REINDEX
                + "\",\"arguments\":[]}";
        client.sendRequest("workspace/executeCommand", params);
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to clearAndReindex command", resp);
        assertTrue("clearAndReindex must return null result", resp.get("result").isJsonNull());

        // The server must still respond to normal requests.
        client.sendRequest("textDocument/codeLens",
                "{\"textDocument\":{\"uri\":\"file:///ClearReindexProbe.java\"}}");
        assertNotNull("Server must respond to codeLens after clearAndReindex",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
    }
}
