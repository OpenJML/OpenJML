package org.openjml.lsp.test;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.OpenJMLLanguageServer;

import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-level tests for {@code textDocument/rename} and
 * {@code textDocument/prepareRename}.
 *
 * <p>These tests send real LSP messages over a pipe, exercising the dispatch
 * path in {@code OpenJMLTextDocumentService.rename()} and
 * {@code prepareRename()} that the direct-API rename tests do not reach.
 */
public class RenameProtocolTest {

    private static final long TIMEOUT_SECONDS = 60;
    private static final long SHORT_TIMEOUT   = 10;

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

    /**
     * Send {@code textDocument/rename} for a simple Java field and assert that
     * the server returns a non-null {@code WorkspaceEdit} containing changes for
     * the file.  This exercises the full protocol dispatch path through
     * {@code OpenJMLTextDocumentService.rename()}.
     */
    @Test
    public void testRenameOverWire_returnsWorkspaceEdit() throws Exception {
        String uri = "file:///RenameProto.java";
        String source =
                "public class RenameProto {\n"
                + "    public int value;\n"
                + "    //@ requires value >= 0;\n"
                + "    public int get() { return value; }\n"
                + "}\n";

        didOpen(uri, source);

        // Wait for the initial --check to complete so the server has an attributed
        // AST; rename requires a resolved symbol and will fail with "No renameable
        // symbol at cursor" if the AST is not yet available.
        waitForDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // prepareRename at "value" on line 1, col 15
        client.sendRequest("textDocument/prepareRename",
                "{\"textDocument\":{\"uri\":\"" + jsonEscape(uri) + "\"},"
                + "\"position\":{\"line\":1,\"character\":15}}");
        JsonObject prepResp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to prepareRename", prepResp);
        assertFalse("prepareRename must not return an error", prepResp.has("error"));

        // rename "value" → "amount" at the same position
        client.sendRequest("textDocument/rename",
                "{\"textDocument\":{\"uri\":\"" + jsonEscape(uri) + "\"},"
                + "\"position\":{\"line\":1,\"character\":15},"
                + "\"newName\":\"amount\"}");
        JsonObject renameResp = client.nextResponse(TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Server must respond to rename", renameResp);
        assertFalse("rename must not return an error: " + renameResp, renameResp.has("error"));

        JsonElement result = renameResp.get("result");
        assertNotNull("rename result must not be null", result);
        assertFalse("rename result must not be JSON null", result.isJsonNull());

        JsonObject edit = result.getAsJsonObject();
        assertTrue("WorkspaceEdit must contain 'changes'", edit.has("changes"));
        JsonObject changes = edit.getAsJsonObject("changes");
        assertTrue("Changes must include the renamed file",
                changes.has(uri));
        assertTrue("Changes for the file must be non-empty",
                changes.getAsJsonArray(uri).size() > 0);
    }

    /**
     * Send {@code textDocument/rename} for an invalid new name (a Java keyword).
     * The server must return an error response, not crash.
     */
    @Test
    public void testRenameOverWire_invalidNameReturnsError() throws Exception {
        String uri = "file:///RenameProtoErr.java";
        String source =
                "public class RenameProtoErr {\n"
                + "    public int count;\n"
                + "}\n";

        didOpen(uri, source);

        client.sendRequest("textDocument/rename",
                "{\"textDocument\":{\"uri\":\"" + jsonEscape(uri) + "\"},"
                + "\"position\":{\"line\":1,\"character\":15},"
                + "\"newName\":\"class\"}");
        JsonObject renameResp = client.nextResponse(TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Server must respond to rename with invalid name", renameResp);
        // Server should return either an error or a null result — must not hang or crash.
        boolean isError  = renameResp.has("error");
        boolean isNull   = renameResp.has("result") && renameResp.get("result").isJsonNull();
        assertTrue("Rename to keyword must return error or null result", isError || isNull);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    /** Wait for any {@code textDocument/publishDiagnostics} notification for {@code uri}. */
    private void waitForDiagsForUri(String uri, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return;
            String msgUri = msg.getAsJsonObject("params").get("uri").getAsString();
            if (uri.equals(msgUri)) return;
        }
    }

    private void didOpen(String uri, String source) throws Exception {
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}");
    }
}
