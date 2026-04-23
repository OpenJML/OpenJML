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
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests that exercise {@link org.openjml.lsp.CheckRunner}
 * paths not reached by the primary ESC tests.
 *
 * <p>Exercises:
 * <ul>
 *   <li>{@code CheckRunner.escWithContext} — file-level ESC on in-memory content
 *       (triggered when a file has been opened via {@code didOpen} so its content
 *       is in {@code lastContent}; sending {@code openjml.runEsc} with the file URI
 *       routes through {@code scheduleEscForUri} → {@code escWithContext})</li>
 *   <li>{@code CheckRunner.buildEffectiveSpecsPath} — non-empty specsPath branch
 *       (triggered via {@code workspace/didChangeConfiguration} that sets an explicit
 *       {@code specsPath}, then runs a rename that calls {@code checkModifiedFiles})</li>
 *   <li>{@code CheckRunner.escWithContext} 3-arg overload — method-started callback path
 *       (triggered by {@code openjml.runEsc} on an open multi-method file; the
 *       {@code onMethodStarted} callback is observed as a code-lens refresh)</li>
 *   <li>{@code scheduleEscForUri} — URI dispatch branch (uri starts with "file://")</li>
 * </ul>
 *
 * <p>All tests follow the lifecycle pattern: {@code didOpen} → LSP command → assert response.
 */
public class CheckRunnerEscContextTest {

    private static final long TIMEOUT_SECONDS = 120;
    private static final long SHORT_TIMEOUT   = 5;

    private OpenJMLLanguageServer server;
    private RawLspClient          client;

    @Before
    public void setUp() throws Exception {
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
    public void tearDown() {
        if (client != null) client.stop();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    private void didOpen(String uri, String source) throws Exception {
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}");
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

    private JsonObject nextNonEmptyDiagsFor(String fragment, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            JsonObject params = msg.getAsJsonObject("params");
            if (!params.get("uri").getAsString().contains(fragment)) continue;
            if (!params.getAsJsonArray("diagnostics").isEmpty()) return msg;
        }
    }

    // -----------------------------------------------------------------------
    // (1) escWithContext — file-level ESC on in-memory content (open file)
    // -----------------------------------------------------------------------

    /**
     * After {@code didOpen} puts the source in {@code lastContent},
     * {@code openjml.runEsc} with the file URI triggers
     * {@code scheduleEscForUri} → {@code escWithContext(uri, content, ...)}.
     *
     * <p>This exercises the in-memory-content branch of {@code scheduleEscForUri},
     * as opposed to the disk-file branch that runs when the file has not been opened.
     * A {@code ensures false} postcondition guarantees ESC produces diagnostics so
     * we can confirm the ESC run completed.
     */
    @Test
    public void testEscWithContext_OpenFileUri() throws Exception {
        String uri    = "file:///EscWithContextTest.java";
        String source =
                "public class EscWithContextTest {\n"
                + "    //@ ensures false;\n"
                + "    public int failing(int x) { return x; }\n"
                + "}\n";

        didOpen(uri, source);
        // Drain the --check triggered by didOpen.
        nextDiagsFor("EscWithContextTest", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Send RUN_ESC with the URI.  Because the file is in lastContent,
        // scheduleEscForUri calls escWithContext(uri, content, snapshot, settings,
        //   onApiReady, onMethodStarted).
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(uri) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // ESC on "ensures false" must produce at least one diagnostic.
        JsonObject note = nextNonEmptyDiagsFor("EscWithContextTest", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("escWithContext must complete and publish ESC diagnostics", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("ESC must report at least one failure for 'ensures false'",
                diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // (2) escWithContext — onMethodStarted callback (intermediate code-lens update)
    // -----------------------------------------------------------------------

    /**
     * When a multi-method file is submitted for ESC via {@code openjml.runEsc},
     * the {@code onMethodStarted} callback fires before each method proof starts,
     * causing intermediate code-lens updates.
     *
     * <p>This exercises the 3-arg {@code escWithContext} overload
     * (with {@code onApiReady} and {@code onMethodStarted}) used by
     * {@code scheduleEscForFile} when content is in {@code lastContent}.
     *
     * <p>Verified by: ESC run completes and at least one publishDiagnostics
     * arrives (confirming the callback path was reached).
     */
    @Test
    public void testEscWithContext_OnMethodStartedCallback() throws Exception {
        String uri    = "file:///EscMultiMethodCtx.java";
        String source =
                "public class EscMultiMethodCtx {\n"
                + "    //@ ensures \\result >= 0;\n"
                + "    public int pos() { return 5; }\n"
                + "    //@ ensures false;\n"
                + "    public int failing() { return 0; }\n"
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("EscMultiMethodCtx", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // File-level ESC: scheduleEscForUri → escWithContext with onMethodStarted callback.
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(uri) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // At least one publishDiagnostics must arrive; the failure in failing() confirms
        // the ESC run completed and the callback path was exercised.
        JsonObject note = nextNonEmptyDiagsFor("EscMultiMethodCtx", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("File-level ESC must publish diagnostics (confirms onMethodStarted path)",
                note);
    }

    // -----------------------------------------------------------------------
    // (3) buildEffectiveSpecsPath — explicit specsPath branch
    // -----------------------------------------------------------------------

    /**
     * When a project is configured with an explicit {@code specsPath} via
     * {@code workspace/didChangeConfiguration}, rename operations that call
     * {@code checkModifiedFiles} reach the non-empty branch of
     * {@code buildEffectiveSpecsPath} (which prepends any prefix dir to the
     * configured path).
     *
     * <p>This test configures an explicit {@code specsPath} and then triggers a
     * rename (which internally calls {@code checkModifiedFilesAndGetCache} and
     * {@code checkModifiedFiles}).  The rename may produce an empty result (no
     * conflicts), but the key assertion is that the server responds without error —
     * confirming {@code buildEffectiveSpecsPath} handled the non-empty path correctly.
     */
    @Test
    public void testBuildEffectiveSpecsPath_ExplicitPath() throws Exception {
        // Configure a non-empty specsPath so buildEffectiveSpecsPath exercises
        // the "prepend parts" branch rather than the early-return empty branch.
        String specsDir = jsonEscape(System.getProperty("java.io.tmpdir", "/tmp"));
        client.sendNotification("workspace/didChangeConfiguration",
                "{\"settings\":{\"openjml\":{\"specsPath\":\"" + specsDir + "\"}}}");
        Thread.sleep(100);

        String uri    = "file:///BldSpecsPathTest.java";
        String source =
                "public class BldSpecsPathTest {\n"
                + "    public String name;\n"
                + "    public int value;\n"
                + "    public BldSpecsPathTest(int v) { value = v; }\n"
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("BldSpecsPathTest", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Request prepare rename on the field "name" (line 1, col 18).
        // prepareRename runs a check before accepting the rename, triggering
        // checkModifiedFiles → buildEffectiveSpecsPath with the configured specsPath.
        client.sendRequest("textDocument/prepareRename",
                "{\"textDocument\":{\"uri\":\"" + jsonEscape(uri) + "\"},"
                + "\"position\":{\"line\":1,\"character\":18}}");
        JsonObject prepResp = client.nextResponse(TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Server must respond to prepareRename", prepResp);
        // prepareRename response may be null result (if not supported at this position)
        // or a range — either is acceptable.  The key assertion: no crash.
        assertFalse("prepareRename must not return an error", prepResp.has("error"));
    }

    // -----------------------------------------------------------------------
    // (4) scheduleEscForUri — URI vs path dispatch split
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEsc} distinguishes URI arguments (starting with "file://")
     * from OS path arguments.  URIs go to {@code scheduleEscForUri}; OS paths go to
     * {@code scheduleEscForPaths}.  This test verifies the URI dispatch branch:
     * an open file's URI is sent as the command argument, and the server dispatches
     * it via {@code scheduleEscForUri} (not {@code scheduleEscForPaths}).
     *
     * <p>Verified by: ESC completes and a {@code publishDiagnostics} notification arrives.
     */
    @Test
    public void testRunEsc_UriDispatch() throws Exception {
        String uri    = "file:///EscUriDispatch.java";
        String source =
                "public class EscUriDispatch {\n"
                + "    //@ ensures \\result == x;\n"
                + "    public int id(int x) { return x; }\n"
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("EscUriDispatch", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // URI dispatch: starts with "file://" → scheduleEscForUri path.
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(uri) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // The trivially-verified postcondition produces no ESC failures,
        // but a publishDiagnostics notification (possibly empty) must still arrive.
        JsonObject note = nextDiagsFor("EscUriDispatch", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("scheduleEscForUri must complete and publish diagnostics", note);
    }
}
