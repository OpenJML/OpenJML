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
 *   <li>{@link #testIndexProjectWithProjectRoots} — configure a
 *       {@code "__workspace__"} project via {@code didChangeConfiguration}, then
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

    private static String fileUri(Path path) {
        return path.toUri().toString();
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
     * Configure a {@code "__workspace__"} project via {@code workspace/didChangeConfiguration}.
     * This is the standard way for single-project clients (VS Code, bare LSP) to inform
     * the server about their source roots after the workspace folder unification.
     */
    private void configureProjectRoots(String osPath) throws Exception {
        String escaped = jsonEscapePath(osPath);
        String settingsJson = "{\"openjml\":{\"projects\":[{\"id\":\"__workspace__\","
                + "\"rootPaths\":[\"" + escaped + "\"]}]}}";
        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":" + settingsJson + "}");
        // Brief pause to let the server apply the settings.
        Thread.sleep(100);
    }

    // -----------------------------------------------------------------------
    // Test 1: indexProject with workspaceFolderPaths
    // -----------------------------------------------------------------------

    /**
     * Configure a {@code "__workspace__"} project pointing to {@code tmpDir}, create a
     * Java file with a type error in that directory, then send
     * {@code openjml.indexProject}.
     *
     * <p>The server's {@link org.openjml.lsp.OpenJMLTextDocumentService#indexProject}
     * collects source directories from the project's {@code rootPaths}, submits
     * {@code runProjectCheck(roots, s)} on the executor, and
     * {@code runProjectCheck} calls {@code CheckRunner.runCheckDirWithContext} and
     * publishes diagnostics for files that produced errors.  The type-error file must
     * appear in a {@code textDocument/publishDiagnostics} notification.
     */
    @Test
    public void testIndexProjectWithProjectRoots() throws Exception {
        write("IndexError.java",
                "public class IndexError {\n"
                + "    public int m() { return \"not an int\"; }\n"
                + "}\n");

        configureProjectRoots(tmpDir.toAbsolutePath().toString());

        // Send openjml.indexProject with no arguments (cmdProject returns null;
        // indexProject(null) uses the projects list as source roots).
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

    // -----------------------------------------------------------------------
    // Test 4: clearAndReindex must NOT re-check stale lastContent
    // -----------------------------------------------------------------------

    /**
     * Verifies that {@code openjml.clearAndReindex} does <em>not</em> re-check
     * open files from the server's cached {@code lastContent} map.
     *
     * <p>Scenario:
     * <ol>
     *   <li>{@code CleanOnDisk.java} is written to disk with no errors.</li>
     *   <li>The editor opens it (clean) then sends a full-text {@code didChange}
     *       that introduces a type error — making the editor "dirty".</li>
     *   <li>{@code AlwaysError.java} is written to disk with a permanent type
     *       error; it is used as a synchronisation marker to confirm that
     *       {@code indexProject} has completed its disk scan.</li>
     *   <li>{@code clearAndReindex} is sent.  A real Eclipse client would follow
     *       this with fresh {@code didChange} for its dirty editors, but in this
     *       test we deliberately omit that step.</li>
     *   <li>All {@code publishDiagnostics} notifications are collected until
     *       {@code AlwaysError.java} errors arrive (proving the disk scan ran)
     *       plus a 2-second drain window.</li>
     * </ol>
     *
     * <p>Expected (after fix): {@code CleanOnDisk.java} produces <em>no</em>
     * error diagnostics, because the server reads the disk (clean) rather than
     * re-checking the dirty editor content stored in {@code lastContent}.
     *
     * <p>With the bug: the server re-checks every entry in {@code lastContent}
     * immediately after the clear, so the dirty error content fires before (or
     * interleaved with) the disk scan and produces spurious error diagnostics.
     */
    @Test
    public void testClearAndReindexDoesNotRecheckStaleEditorContent() throws Exception {
        // CleanOnDisk.java: no errors on disk; dirty editor version has a type error.
        final String cleanContent =
                "public class CleanOnDisk {\n"
                + "    public int m() { return 42; }\n"
                + "}\n";
        final String dirtyContent =
                "public class CleanOnDisk {\n"
                + "    public int m() { return \"dirty type error\"; }\n"
                + "}\n";
        // AlwaysError.java: permanent type error on disk; functions as a marker.
        final String errorContent =
                "public class AlwaysError {\n"
                + "    public int m() { return \"disk error\"; }\n"
                + "}\n";

        write("CleanOnDisk.java", cleanContent);
        write("AlwaysError.java", errorContent);
        String cleanUri = fileUri(tmpDir.resolve("CleanOnDisk.java"));

        // --- Correct clearAndReindex protocol step 1: send current project config ---
        configureProjectRoots(tmpDir.toAbsolutePath().toString());

        // Open CleanOnDisk.java (disk content, no errors) and drain initial check.
        String openParams = "{\"textDocument\":{\"uri\":\"" + cleanUri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(cleanContent) + "\"}}";
        client.sendNotification("textDocument/didOpen", openParams);
        nextDiagsFor("CleanOnDisk", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Make the editor dirty: full-text didChange introducing a type error.
        String changeParams = "{\"textDocument\":{\"uri\":\"" + cleanUri + "\",\"version\":2},"
                + "\"contentChanges\":[{\"text\":\"" + jsonEscape(dirtyContent) + "\"}]}";
        client.sendNotification("textDocument/didChange", changeParams);
        JsonObject dirtyDiags = nextDiagsFor("CleanOnDisk", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected error diagnostics after dirty edit", dirtyDiags);
        assertFalse("Dirty content must produce type errors",
                dirtyDiags.getAsJsonObject("params").getAsJsonArray("diagnostics").isEmpty());

        Thread.sleep(500);   // let background work settle

        // --- Correct clearAndReindex protocol step 2: send clearAndReindex ---
        // (A real Eclipse client would follow this with fresh didChange for dirty
        // editors, but here we omit that to verify the server does NOT re-check
        // from lastContent on its own.)
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.CLEAR_AND_REINDEX + "\",\"arguments\":[]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Drain all publishDiagnostics notifications that arrive after the clear.
        // AlwaysError.java (errors on disk) is the synchronisation marker:
        // once its error diagnostics arrive, the disk scan (indexProject) is done.
        // We then drain for 2 more seconds to catch any late CleanOnDisk.java events.
        boolean sawAlwaysError     = false;
        boolean cleanOnDiskHadErrors = false;
        long deadline    = System.nanoTime() + TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS);
        long extraDeadline = Long.MAX_VALUE;

        while (System.nanoTime() < Math.min(deadline, extraDeadline)) {
            long remaining = Math.min(deadline, extraDeadline) - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject notif = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (notif == null) break;
            JsonObject p   = notif.getAsJsonObject("params");
            String    uri  = p.get("uri").getAsString();
            JsonArray diags = p.getAsJsonArray("diagnostics");

            if (uri.contains("CleanOnDisk") && !diags.isEmpty()) {
                cleanOnDiskHadErrors = true;   // spurious re-check of dirty lastContent
            }
            if (uri.contains("AlwaysError") && !diags.isEmpty()) {
                sawAlwaysError = true;
                // Give 2 more seconds for any late CleanOnDisk.java notifications.
                extraDeadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(2);
            }
        }

        assertTrue("indexProject must complete and publish errors for AlwaysError.java "
                + "(confirms disk scan ran after clearAndReindex)", sawAlwaysError);
        assertFalse("clearAndReindex must not re-check stale editor content: "
                + "CleanOnDisk.java is clean on disk; the dirty type error from the "
                + "editor must not be published after the reset (no lastContent re-check).",
                cleanOnDiskHadErrors);
    }
}
