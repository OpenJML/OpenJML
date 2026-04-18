package org.openjml.lsp.test;

import com.google.gson.JsonArray;
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
 * Protocol-level tests for {@code textDocument/documentSymbol}.
 *
 * <p>These tests send real LSP messages over a pipe, exercising the full
 * dispatch path through {@code OpenJMLTextDocumentService} that the
 * direct-API tests in {@link DocumentSymbolTest} do not reach.
 *
 * <p>OpenJML's document-symbol provider returns only JML-specific symbols
 * (ghost fields, model fields, model methods) so that the outline complements
 * rather than duplicates the Java outline provided by the Red Hat extension.
 */
public class DocumentSymbolProtocolTest {

    private static final long SHORT_TIMEOUT = 10;
    private static final long TIMEOUT_SECONDS = 30;

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
     * A plain Java class with no JML members must return a well-formed symbol array.
     *
     * <p>The default server setting ({@code useIntegratedOutline=true}) returns all
     * Java symbols, so the class itself appears as a top-level symbol even when it
     * has no JML children.  The test verifies the full protocol dispatch path and
     * that at least one symbol named "DocSymProto" is present.
     */
    @Test
    public void testDocumentSymbol_plainJavaClass_returnsClassSymbol() throws Exception {
        String uri = "file:///DocSymProto.java";
        String source =
                "public class DocSymProto {\n"
                + "    public int value;\n"
                + "    public int getValue() { return value; }\n"
                + "}\n";

        didOpen(uri, source);

        client.sendRequest("textDocument/documentSymbol",
                "{\"textDocument\":{\"uri\":\"" + jsonEscape(uri) + "\"}}");
        JsonObject resp = client.nextResponse(TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Server must respond to documentSymbol", resp);
        assertFalse("documentSymbol must not return an error: " + resp, resp.has("error"));

        JsonElement result = resp.get("result");
        assertNotNull("documentSymbol result field must be present", result);
        assertFalse("documentSymbol result must not be JSON null", result.isJsonNull());

        JsonArray symbols = result.getAsJsonArray();
        assertTrue("Expected at least one symbol (the class itself) for a plain Java class",
                symbols.size() > 0);
        boolean foundClass = findSymbolNamed(symbols, "DocSymProto");
        assertTrue("Expected a symbol named 'DocSymProto'", foundClass);
    }

    /**
     * A class containing a JML ghost field and a model method must return symbols
     * for those JML members, exercising the full protocol dispatch path through
     * {@code OpenJMLTextDocumentService.documentSymbol()}.
     */
    @Test
    public void testDocumentSymbol_jmlMembers_returnsSymbols() throws Exception {
        String uri = "file:///DocSymProtoJml.java";
        String source =
                "public class DocSymProtoJml {\n"
                + "    //@ ghost public int count;\n"
                + "    /*@ model public int total;\n"
                + "      @ model public int getTotal() { return total; }\n"
                + "      @*/\n"
                + "    public int value;\n"
                + "}\n";

        didOpen(uri, source);

        client.sendRequest("textDocument/documentSymbol",
                "{\"textDocument\":{\"uri\":\"" + jsonEscape(uri) + "\"}}");
        JsonObject resp = client.nextResponse(TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Server must respond to documentSymbol", resp);
        assertFalse("documentSymbol must not return an error: " + resp, resp.has("error"));

        JsonElement result = resp.get("result");
        assertNotNull("documentSymbol result must not be absent", result);
        assertFalse("documentSymbol for JML class must not be JSON null", result.isJsonNull());

        JsonArray symbols = result.getAsJsonArray();
        assertTrue("Expected at least one symbol for a class with JML members",
                symbols.size() > 0);

        // At least one of the declared JML members must appear somewhere in the tree.
        assertTrue("Expected to find at least one JML symbol (ghost/model)",
                findSymbolNamed(symbols, "count")
                || findSymbolNamed(symbols, "total")
                || findSymbolNamed(symbols, "getTotal"));
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static boolean findSymbolNamed(JsonArray symbols, String name) {
        for (JsonElement elem : symbols) {
            JsonObject sym = elem.getAsJsonObject();
            if (name.equals(sym.get("name").getAsString())) return true;
            if (sym.has("children")) {
                if (findSymbolNamed(sym.getAsJsonArray("children"), name)) return true;
            }
        }
        return false;
    }

    private static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    private void didOpen(String uri, String source) throws Exception {
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}");
    }
}
