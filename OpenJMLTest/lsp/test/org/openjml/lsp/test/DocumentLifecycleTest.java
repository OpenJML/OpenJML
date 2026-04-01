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
 * Protocol-layer tests for the document-lifecycle notifications:
 * {@code textDocument/didOpen}, {@code textDocument/didChange}, and
 * {@code textDocument/didClose}.
 *
 * <p>Each test drives an in-process LSP server through the full JSON-RPC path
 * via {@link RawLspClient} and asserts on the resulting
 * {@code textDocument/publishDiagnostics} notifications.  This verifies that
 * the server's document-tracking wiring (content storage, scheduler dispatch)
 * is intact end-to-end, complementing the direct-API tests in
 * {@link DiagnosticsTest}.
 */
public class DocumentLifecycleTest {

    private static final long TIMEOUT_SECONDS = 120;
    private static final long SHORT_TIMEOUT   = 5;

    private OpenJMLLanguageServer server;
    private RawLspClient          client;

    // -----------------------------------------------------------------------
    // Setup / teardown
    // -----------------------------------------------------------------------

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
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to initialize", resp);
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
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\","
                + "\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}";
        client.sendNotification("textDocument/didOpen", params);
    }

    private void didChange(String uri, int version, String source) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\",\"version\":" + version + "},"
                + "\"contentChanges\":[{\"text\":\"" + jsonEscape(source) + "\"}]}";
        client.sendNotification("textDocument/didChange", params);
    }

    private void didClose(String uri) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\"}}";
        client.sendNotification("textDocument/didClose", params);
    }

    /** Wait for the next publishDiagnostics whose URI contains {@code uriFragment}. */
    private JsonObject nextDiagsFor(String uriFragment, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            if (msg.getAsJsonObject("params").get("uri").getAsString().contains(uriFragment))
                return msg;
        }
    }

    // -----------------------------------------------------------------------
    // textDocument/didOpen
    // -----------------------------------------------------------------------

    /**
     * {@code textDocument/didOpen} with a type-error source must trigger
     * {@code textDocument/publishDiagnostics} containing Error-severity diagnostics.
     */
    @Test
    public void testDidOpenErrorTriggersPublishDiagnostics() throws Exception {
        String uri = "file:///DLCOpenErr.java";
        String source =
                "public class DLCOpenErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";
        didOpen(uri, source);

        JsonObject note = nextDiagsFor("DLCOpenErr", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen of erroneous file", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one diagnostic", diags.isEmpty());
    }

    /**
     * {@code textDocument/didOpen} with clean Java source must trigger
     * {@code textDocument/publishDiagnostics} with an empty diagnostics array.
     */
    @Test
    public void testDidOpenCleanFilePublishesEmptyDiagnostics() throws Exception {
        String uri = "file:///DLCOpenClean.java";
        String source =
                "public class DLCOpenClean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n";
        didOpen(uri, source);

        JsonObject note = nextDiagsFor("DLCOpenClean", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen of clean file", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("Expected empty diagnostics for clean file", diags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // textDocument/didChange
    // -----------------------------------------------------------------------

    // -----------------------------------------------------------------------
    // textDocument/completion
    // -----------------------------------------------------------------------

    /**
     * Sending {@code textDocument/completion} with the cursor inside a JML
     * annotation ({@code //@ req}) must return a non-empty list of completion
     * items that includes {@code requires}.  This exercises the wiring in
     * {@link org.openjml.lsp.OpenJMLTextDocumentService#completion} and confirms
     * that the server advertises and correctly routes completion requests.
     *
     * <p>The response {@code result} may be a JSON array (list form) or a JSON
     * object with an {@code items} array (CompletionList form); both are handled.
     */
    @Test
    public void testCompletionInsideJmlAnnotationReturnsKeywords() throws Exception {
        String uri = "file:///DLCCompletion.java";
        // line 0: "public class DLCCompletion {"
        // line 1: "    //@ req"   ← cursor at end (col 11), inside JML annotation
        // line 2: "    public void m() {}"
        // line 3: "}"
        String source =
                "public class DLCCompletion {\n" +
                "    //@ req\n" +
                "    public void m() {}\n" +
                "}\n";
        didOpen(uri, source);
        // Drain the initial publishDiagnostics before sending the completion request
        // so it does not interfere with the response queue.
        nextDiagsFor("DLCCompletion", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Send textDocument/completion: cursor at line 1, col 11 (end of "//@ req")
        String params =
                "{\"textDocument\":{\"uri\":\"" + uri + "\"}," +
                "\"position\":{\"line\":1,\"character\":11}," +
                "\"context\":{\"triggerKind\":1}}";
        client.sendRequest("textDocument/completion", params);

        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to textDocument/completion", resp);
        assertTrue("Response must have a result field", resp.has("result"));

        // result may be an array (List<CompletionItem>) or object (CompletionList)
        JsonElement result = resp.get("result");
        JsonArray items;
        if (result.isJsonArray()) {
            items = result.getAsJsonArray();
        } else {
            items = result.getAsJsonObject().getAsJsonArray("items");
        }
        assertNotNull("Completion result must contain an items array", items);
        assertFalse("Expected at least one completion item inside JML annotation", items.isEmpty());

        boolean hasRequires = false;
        for (JsonElement el : items) {
            if ("requires".equals(el.getAsJsonObject().get("label").getAsString())) {
                hasRequires = true;
                break;
            }
        }
        assertTrue("'requires' must appear in completions inside a JML annotation", hasRequires);
    }

    /**
     * Changing a previously clean file to introduce a type error must trigger
     * a new {@code textDocument/publishDiagnostics} with error diagnostics.
     */
    @Test
    public void testDidChangeIntroducingErrorTriggersDiagnostics() throws Exception {
        String uri = "file:///DLCChange.java";

        // Open clean — consume the initial empty publishDiagnostics
        String cleanSource =
                "public class DLCChange {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n";
        didOpen(uri, cleanSource);
        nextDiagsFor("DLCChange", TIMEOUT_SECONDS, TimeUnit.SECONDS); // drain initial publish

        // Change to a type error
        String errSource =
                "public class DLCChange {\n" +
                "    public int add(int a, int b) { return \"wrong\"; }\n" +
                "}\n";
        didChange(uri, 2, errSource);

        JsonObject note = nextDiagsFor("DLCChange", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didChange introducing error", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one error diagnostic after change", diags.isEmpty());
    }
}
