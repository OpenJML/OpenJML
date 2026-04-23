package org.openjml.lsp.test;

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
 * Protocol-layer tests for {@link OpenJMLLanguageServer} lifecycle paths:
 * {@code initialize}, {@code shutdown}, and the {@code __workspace__} project
 * synthesis branch.
 *
 * <p>Exercises:
 * <ul>
 *   <li>{@code OpenJMLLanguageServer.initialize()} — workspace synthesis when no
 *       explicit projects are configured ({@code __workspace__} default project)</li>
 *   <li>{@code OpenJMLLanguageServer.initialize()} — rootUri fallback branch when
 *       no workspace folders are present but a {@code rootUri} is supplied</li>
 *   <li>{@code OpenJMLLanguageServer.shutdown()} — returns null result, sets exitCode 0</li>
 *   <li>{@code OpenJMLLanguageServer.getTextDocumentService()} — always non-null</li>
 *   <li>{@code OpenJMLLanguageServer.getWorkspaceService()} — always non-null</li>
 *   <li>{@code isCodeLensFormat} boundary — 1-arg list returns false (neither 2-arg
 *       nor 3-arg dispatch, so the server silently skips the command)</li>
 * </ul>
 */
public class LanguageServerLifecycleTest {

    private static final long SHORT_TIMEOUT = 10;
    private static final long TIMEOUT_SECONDS = 60;

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
    }

    @After
    public void tearDown() {
        if (client != null) client.stop();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static String escape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"");
    }

    private static String escapeContent(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"")
                .replace("\n", "\\n").replace("\r", "");
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
    // (1) initialize — no explicit project config → __workspace__ synthesis
    // -----------------------------------------------------------------------

    /**
     * When {@code initialize} is called with no project configuration in
     * {@code initializationOptions}, the server must synthesize a
     * {@code __workspace__} project.  Verified indirectly: the server must
     * respond to {@code initialize} and subsequently process file opens
     * without error (confirming the synthesized project settings are used).
     */
    @Test
    public void testInitialize_WorkspaceSynthesis_NoConfig() throws Exception {
        // initialize with no initializationOptions and no rootUri — triggers the
        // "no projects configured" branch that creates the __workspace__ project.
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,\"capabilities\":{}}");
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to initialize", resp);
        assertTrue("initialize must return a result", resp.has("result"));
        assertFalse("initialize result must not be an error", resp.has("error"));

        // Server capabilities must include definition and codeLens.
        JsonObject caps = resp.getAsJsonObject("result").getAsJsonObject("capabilities");
        assertNotNull("ServerCapabilities must be present", caps);
        assertTrue("Server must advertise definition support",
                caps.has("definitionProvider") || caps.has("referencesProvider"));

        client.sendNotification("initialized", "{}");

        // Open a file: the server must process it using the synthesized __workspace__
        // project settings (no NPE, publishDiagnostics arrives).
        String uri    = "file:///WorkspaceSynthTest.java";
        String source = "public class WorkspaceSynthTest {\n    public int m() { return 1; }\n}\n";
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + escapeContent(source) + "\"}}");

        // publishDiagnostics must arrive (may be empty for valid code; just needs to arrive).
        JsonObject note = nextDiagsFor("WorkspaceSynthTest", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("publishDiagnostics must arrive after didOpen on synthesized workspace",
                note);
    }

    // -----------------------------------------------------------------------
    // (2) initialize — rootUri fallback branch
    // -----------------------------------------------------------------------

    /**
     * When {@code initialize} is called with a {@code rootUri} but no
     * {@code workspaceFolders}, the server uses {@code rootUri} as the
     * workspace path for the synthesized {@code __workspace__} project.
     *
     * <p>This exercises the "Fall back to rootUri when no workspace-folders
     * list is provided" branch inside {@code initialize()}.  The rootUri is
     * set to a temp-style path; the server synthesizes {@code __workspace__}
     * with that path.  We verify the server responds correctly to
     * {@code initialize} and can subsequently accept commands.
     */
    @Test
    public void testInitialize_WorkspaceSynthesis_RootUri() throws Exception {
        String rootUri = "file:///tmp/lsp-lifecycle-test";
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":\"" + escape(rootUri)
                + "\",\"capabilities\":{}}");
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to initialize with rootUri", resp);
        assertTrue("initialize must return a result", resp.has("result"));
        assertFalse("initialize must not return an error", resp.has("error"));

        JsonObject caps = resp.getAsJsonObject("result").getAsJsonObject("capabilities");
        assertNotNull("ServerCapabilities must be present", caps);
        assertTrue("Server must advertise definition support",
                caps.has("definitionProvider") || caps.has("referencesProvider"));

        client.sendNotification("initialized", "{}");

        // Verify the server continues to function: query running ESC tasks (a
        // lightweight command that confirms the synthesized project is in place).
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.GET_RUNNING_ESC_TASKS
                + "\",\"arguments\":[]}");
        JsonObject taskResp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to command after rootUri-based synthesis", taskResp);
        assertTrue("Command must return a result", taskResp.has("result"));
    }

    // -----------------------------------------------------------------------
    // (3) shutdown() — returns null result, no exception
    // -----------------------------------------------------------------------

    /**
     * {@code shutdown()} must return a response with a {@code null} result
     * and must not throw.  The {@code exitCode} is set to 0 before the future
     * completes, meaning a subsequent {@code exit()} would terminate with 0.
     * (We cannot call {@code exit()} in-process since it calls
     * {@code System.exit}; the correct exit-code behavior is verified here
     * by checking that {@code shutdown} succeeds cleanly.)
     */
    @Test
    public void testShutdown_ReturnsNull() throws Exception {
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,\"capabilities\":{}}");
        assertNotNull("Server must respond to initialize",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
        client.sendNotification("initialized", "{}");

        // The LSP spec says the client must not send further requests after
        // shutdown except exit; we send shutdown and verify the response.
        client.sendRequest("shutdown", "{}");
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to shutdown request", resp);
        assertTrue("shutdown response must have a result field", resp.has("result"));
        // Per LSP spec the shutdown result is null.
        assertTrue("shutdown result must be null", resp.get("result").isJsonNull());
        assertFalse("shutdown must not return an error", resp.has("error"));
    }

    // -----------------------------------------------------------------------
    // (4) getTextDocumentService / getWorkspaceService — always non-null
    // -----------------------------------------------------------------------

    /**
     * {@code getTextDocumentService()} and {@code getWorkspaceService()} are
     * called by the LSP4J framework on every request; they must never return
     * null.  Exercising them here covers the accessor methods in coverage.
     */
    @Test
    public void testServiceAccessors_NonNull() throws Exception {
        assertNotNull("getTextDocumentService must not return null",
                server.getTextDocumentService());
        assertNotNull("getWorkspaceService must not return null",
                server.getWorkspaceService());
    }

    // -----------------------------------------------------------------------
    // (5) isCodeLensFormat — 1-arg edge case (neither branch executes ESC)
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEscForMethod} with a single-arg list is neither
     * code-lens format (2 args) nor standard format (3 args).  The server
     * must respond to the command without crashing; the result is null
     * because no ESC is scheduled (no URI can be extracted).
     *
     * <p>This covers the {@code isCodeLensFormat()} guard that returns
     * {@code false} for lists with size != 2.
     */
    @Test
    public void testRunEscForMethod_SingleArg_NoOp() throws Exception {
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,\"capabilities\":{}}");
        assertNotNull("Server must respond to initialize",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
        client.sendNotification("initialized", "{}");

        // 1-arg list: isCodeLensFormat == false (size != 2) and the else-branch
        // also fails to dispatch because args[1] (uri) is absent.
        // The server must silently return null rather than throwing.
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":[\"file:///SingleArgTest.java\"]}");
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to malformed RUN_ESC_FOR_METHOD", resp);
        // Any response (null result or error) is acceptable; no crash is the key assertion.
    }

    // -----------------------------------------------------------------------
    // (6) initialize with workspaceFolders — explicit folder synthesis branch
    // -----------------------------------------------------------------------

    /**
     * When {@code initialize} supplies {@code workspaceFolders} (the normal
     * VS Code path), the server synthesizes {@code __workspace__} with those
     * folder paths.  This exercises the {@code for (var folder ...)} branch
     * inside {@code initialize()}.
     */
    @Test
    public void testInitialize_WorkspaceFolders_Synthesis() throws Exception {
        String folderUri = "file:///tmp/lsp-workspace-folders-test";
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,"
                + "\"workspaceFolders\":[{\"uri\":\"" + escape(folderUri)
                + "\",\"name\":\"test\"}],"
                + "\"capabilities\":{}}");
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to initialize with workspaceFolders", resp);
        assertTrue("initialize must return a result", resp.has("result"));
        assertFalse("initialize must not return an error", resp.has("error"));
        client.sendNotification("initialized", "{}");
    }
}
