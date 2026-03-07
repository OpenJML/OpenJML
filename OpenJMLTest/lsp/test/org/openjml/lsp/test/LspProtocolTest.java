package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.OpenJMLLanguageServer;

import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * Protocol-layer tests for the OpenJML LSP server.
 *
 * These tests exercise the server's full JSON-RPC stack — Content-Length
 * framing, message routing, and {@code textDocument/publishDiagnostics}
 * responses — using a raw JSON-RPC client ({@link RawLspClient}).
 *
 * LSP4J's in-process {@code Launcher} is used only on the server side.
 * The client side sends hand-crafted JSON messages directly over
 * {@link PipedInputStream}/{@link PipedOutputStream} pipes.  This design
 * avoids the jdk.compiler Gson limitation: jdk.compiler bundles a
 * reflection-disabled Gson, so LSP4J's client-side serialization of types
 * without explicit adapters (e.g., {@code ClientCapabilities}) fails.
 * Using raw JSON bypasses that limitation while still fully exercising the
 * server's receive / parse / process / send path.
 *
 * Each test follows the LSP handshake ({@code initialize} /
 * {@code initialized}), then sends {@code textDocument/didOpen} and waits
 * for the asynchronous {@code textDocument/publishDiagnostics} notification.
 *
 * Note: OpenJML invocation is inherently slow (JVM warm-up, spec loading),
 * so tests use a generous 60-second timeout per check.
 */
public class LspProtocolTest {

    private static final long TIMEOUT_SECONDS = 60;

    private OpenJMLLanguageServer server;
    private RawLspClient          client;

    @Before
    public void setUp() throws Exception {
        // Use large pipe buffers to avoid stalling on big JSON payloads.
        PipedInputStream  serverIn  = new PipedInputStream(65536);
        PipedOutputStream clientOut = new PipedOutputStream(serverIn);
        PipedInputStream  clientIn  = new PipedInputStream(65536);
        PipedOutputStream serverOut = new PipedOutputStream(clientIn);

        server = new OpenJMLLanguageServer();
        var launcher = LSPLauncher.createServerLauncher(server, serverIn, serverOut);
        server.connect(launcher.getRemoteProxy());
        launcher.startListening();

        client = new RawLspClient(clientOut, clientIn);

        // LSP handshake: initialize (minimal params) + initialized
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,\"capabilities\":{}}");
        // Give the server a moment to respond before sending initialized.
        // (We ignore the initialize response — we just need to send it.)
        Thread.sleep(500);
        client.sendNotification("initialized", "{}");
    }

    @After
    public void tearDown() {
        if (client != null) client.stop();
    }

    /** A type error must produce Error-severity diagnostics over the full protocol. */
    @Test
    public void testTypeErrorProducesErrorDiagnosticOverProtocol() throws Exception {
        String uri    = "file:///TypeErrP.java";
        String source = "public class TypeErrP {\\n    public int m() { return \\\"not an int\\\"; }\\n}\\n";

        openDocument(uri, source);

        JsonObject notification =
                client.nextNotification("textDocument/publishDiagnostics",
                        TIMEOUT_SECONDS, TimeUnit.SECONDS);

        assertNotNull("Expected publishDiagnostics notification", notification);
        JsonArray diags = notification.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one diagnostic for type error", diags.isEmpty());

        boolean hasError = false;
        for (var el : diags) {
            // LSP severity 1 = Error
            if (el.getAsJsonObject().has("severity") &&
                    el.getAsJsonObject().get("severity").getAsInt() == 1) {
                hasError = true;
                break;
            }
        }
        assertTrue("Expected at least one Error-severity diagnostic", hasError);
    }

    /** A clean Java file must produce an empty diagnostic list over the full protocol. */
    @Test
    public void testCleanJavaProducesNoDiagnosticsOverProtocol() throws Exception {
        String uri    = "file:///Clean3.java";
        String source = "public class Clean3 {\\n    public int add(int a, int b) { return a + b; }\\n}\\n";

        openDocument(uri, source);

        JsonObject notification =
                client.nextNotification("textDocument/publishDiagnostics",
                        TIMEOUT_SECONDS, TimeUnit.SECONDS);

        assertNotNull("Expected publishDiagnostics notification", notification);
        JsonArray diags = notification.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertEquals("Expected no diagnostics for clean Java source", 0, diags.size());
    }

    // --- helpers ---

    private void openDocument(String uri, String source) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\","
                + "\"languageId\":\"java\",\"version\":1,\"text\":\""
                + source + "\"}}";
        client.sendNotification("textDocument/didOpen", params);
    }
}
