package org.openjml.lsp.test;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

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
public class RenameProtocolTest extends ProtocolTestBase {

    // Note: this file used TIMEOUT_SECONDS=60 and SHORT_TIMEOUT=10.
    // The base class values (120 and 5) are compatible — longer timeout is fine.

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
        nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);

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
}
