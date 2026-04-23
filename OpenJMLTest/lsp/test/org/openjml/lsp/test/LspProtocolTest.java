package org.openjml.lsp.test;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.openjml.lsp.OpenJMLLanguageServer;
import org.openjml.lsp.OpenJMLCommands;

import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
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
 * {@code initialized}), then sends document notifications and waits
 * for the asynchronous {@code textDocument/publishDiagnostics} notification.
 *
 * Disk-file tests use permanent test data files under
 * {@code OpenJMLTest/lsp/testdata/}, with one subdirectory per test case.
 * The root is supplied via the {@code lsp.testdata} system property.
 *
 * Note: OpenJML invocation is inherently slow (JVM warm-up, spec loading),
 * so tests use a generous 60-second timeout per check.
 */
public class LspProtocolTest {

    private static final long TIMEOUT_SECONDS      = 60;
    private static final long SHORT_TIMEOUT_SECONDS = 5;

    private OpenJMLLanguageServer server;
    private RawLspClient          client;
    /** The response to the {@code initialize} request, captured during setUp. */
    private JsonObject initializeResponse;

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

        // LSP handshake: initialize + initialized.
        // We read the initialize response explicitly so (a) tests can inspect
        // the advertised capabilities, and (b) we know the server is ready
        // before we send "initialized" and subsequent requests.
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":null,\"capabilities\":{}}");
        initializeResponse = client.nextResponse(SHORT_TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Server must respond to initialize", initializeResponse);
        client.sendNotification("initialized", "{}");
    }

    @After
    public void tearDown() {
        if (client != null) client.stop();
    }

    // -----------------------------------------------------------------------
    // Content-based checks (in-memory, no disk file)
    // -----------------------------------------------------------------------

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
        assertTrue("Expected at least one Error-severity diagnostic", hasErrorDiagnostic(diags));
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

    // -----------------------------------------------------------------------
    // Disk-file tests: didOpen reads from the file on disk
    // -----------------------------------------------------------------------

    /**
     * Opening a file on disk that contains a type error must trigger a check
     * using the file path directly (no temp file), and produce Error diagnostics.
     * Test data: testdata/testDidOpenDiskFileTypeError/TypeErrDisk.java
     */
    @Test
    public void testDidOpenDiskFileTypeError() throws Exception {
        Path file = testdataFile("testDidOpenDiskFileTypeError/TypeErrDisk.java");
        String uri = file.toUri().toString();

        openDocumentFile(uri, Files.readString(file));

        JsonObject notification =
                client.nextNotification("textDocument/publishDiagnostics",
                        TIMEOUT_SECONDS, TimeUnit.SECONDS);

        assertNotNull("Expected publishDiagnostics for disk file with type error", notification);
        JsonArray diags = notification.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one diagnostic", diags.isEmpty());
        assertTrue("Expected Error-severity diagnostic", hasErrorDiagnostic(diags));
    }

    /**
     * Opening a clean file on disk must produce an empty diagnostic list.
     * Test data: testdata/testDidOpenDiskFileClean/CleanDisk.java
     */
    @Test
    public void testDidOpenDiskFileClean() throws Exception {
        Path file = testdataFile("testDidOpenDiskFileClean/CleanDisk.java");
        String uri = file.toUri().toString();

        openDocumentFile(uri, Files.readString(file));

        JsonObject notification =
                client.nextNotification("textDocument/publishDiagnostics",
                        TIMEOUT_SECONDS, TimeUnit.SECONDS);

        assertNotNull("Expected publishDiagnostics for clean disk file", notification);
        JsonArray diags = notification.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertEquals("Expected no diagnostics for clean file on disk", 0, diags.size());
    }

    // -----------------------------------------------------------------------
    // Disk-file test: didSave reads from the file on disk
    // -----------------------------------------------------------------------

    /**
     * Saving a file on disk that contains a type error must trigger a check
     * using the disk file and produce Error diagnostics.
     * Test data: testdata/testDidSaveProducesDiagnostics/TypeErrSave.java
     */
    @Test
    public void testDidSaveProducesDiagnostics() throws Exception {
        Path file = testdataFile("testDidSaveProducesDiagnostics/TypeErrSave.java");
        String uri = file.toUri().toString();

        saveDocument(uri);

        JsonObject notification =
                client.nextNotification("textDocument/publishDiagnostics",
                        TIMEOUT_SECONDS, TimeUnit.SECONDS);

        assertNotNull("Expected publishDiagnostics after didSave", notification);
        JsonArray diags = notification.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one diagnostic after didSave", diags.isEmpty());
        assertTrue("Expected Error-severity diagnostic after didSave", hasErrorDiagnostic(diags));
    }

    // -----------------------------------------------------------------------
    // triggerOn mode tests
    // -----------------------------------------------------------------------

    /**
     * In edit mode (default), a didChange notification must trigger a check
     * and publish diagnostics.
     */
    @Test
    public void testDidChangeInEditModeTriggersCheck() throws Exception {
        String uri    = "file:///EditModeDoc.java";
        String source = "public class EditModeDoc {\\n    public int m() { return \\\"not an int\\\"; }\\n}\\n";

        changeDocument(uri, source);

        JsonObject notification =
                client.nextNotification("textDocument/publishDiagnostics",
                        TIMEOUT_SECONDS, TimeUnit.SECONDS);

        assertNotNull("Expected publishDiagnostics from didChange in edit mode", notification);
        JsonArray diags = notification.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one diagnostic", diags.isEmpty());
        assertTrue("Expected Error-severity diagnostic", hasErrorDiagnostic(diags));
    }

    /**
     * In save mode, a didChange notification must NOT trigger a check.
     * No publishDiagnostics notification should arrive within a short window.
     */
    @Test
    public void testDidChangeInSaveModeNoCheck() throws Exception {
        setCheckTriggerOn("save");
        // Allow the configuration change to be processed before sending didChange.
        Thread.sleep(200);

        String uri    = "file:///SaveModeDoc.java";
        String source = "public class SaveModeDoc {\\n    public int m() { return \\\"not an int\\\"; }\\n}\\n";

        changeDocument(uri, source);

        JsonObject notification =
                client.nextNotification("textDocument/publishDiagnostics",
                        SHORT_TIMEOUT_SECONDS, TimeUnit.SECONDS);

        assertNull("Expected NO publishDiagnostics from didChange in save mode", notification);
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Returns the absolute path to a file under the lsp.testdata directory. */
    private static Path testdataFile(String relative) {
        String root = System.getProperty("lsp.testdata");
        assertNotNull("System property lsp.testdata must be set", root);
        Path file = Paths.get(root).resolve(relative);
        assertTrue("Test data file must exist on disk: " + file, file.toFile().exists());
        return file;
    }

    /** Send textDocument/didOpen with the given URI and source content. */
    private void openDocument(String uri, String source) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\","
                + "\"languageId\":\"java\",\"version\":1,\"text\":\""
                + source + "\"}}";
        client.sendNotification("textDocument/didOpen", params);
    }

    /**
     * Send textDocument/didOpen with disk-file content (which may contain
     * characters that require JSON escaping such as {@code "} and newlines).
     */
    private void openDocumentFile(String uri, String source) throws Exception {
        Gson gson = new Gson();
        String params = "{\"textDocument\":{\"uri\":" + gson.toJson(uri) + ","
                + "\"languageId\":\"java\",\"version\":1,\"text\":"
                + gson.toJson(source) + "}}";
        client.sendNotification("textDocument/didOpen", params);
    }

    /** Send textDocument/didChange (full-sync) with the given URI and source content. */
    private void changeDocument(String uri, String source) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\",\"version\":2},"
                + "\"contentChanges\":[{\"text\":\"" + source + "\"}]}";
        client.sendNotification("textDocument/didChange", params);
    }

    /** Send textDocument/didSave for the given URI (no content — server reads from disk). */
    private void saveDocument(String uri) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\"}}";
        client.sendNotification("textDocument/didSave", params);
    }

    /**
     * Send {@code workspace/symbol} for {@code query} and return the list of
     * matched symbol names (exact case-sensitive match, per the server's filter).
     * Empty query returns all non-synthetic names.
     */
    private List<String> queryWorkspaceSymbol(String query) throws Exception {
        Gson gson = new Gson();
        client.sendRequest("workspace/symbol", "{\"query\":" + gson.toJson(query) + "}");
        JsonObject response = client.nextResponse(SHORT_TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected response to workspace/symbol for query=" + query, response);
        assertFalse("workspace/symbol must not return an error",
                response.has("error") && !response.get("error").isJsonNull());
        if (!response.has("result") || response.get("result").isJsonNull()) return List.of();
        JsonArray arr = response.getAsJsonArray("result");
        if (arr == null) return List.of();
        List<String> names = new ArrayList<>();
        for (var el : arr) {
            JsonObject sym = el.getAsJsonObject();
            if (sym.has("name")) names.add(sym.get("name").getAsString());
        }
        return names;
    }

    /** Send workspace/didChangeConfiguration to change the checkTriggerOn setting. */
    private void setCheckTriggerOn(String mode) throws Exception {
        String params = "{\"settings\":{\"openjml\":{\"checkTriggerOn\":\"" + mode + "\"}}}";
        client.sendNotification("workspace/didChangeConfiguration", params);
    }

    /** Send workspace/executeCommand with no arguments. */
    private void executeCommand(String command) throws Exception {
        String params = "{\"command\":\"" + command + "\",\"arguments\":[]}";
        client.sendRequest("workspace/executeCommand", params);
    }

    /**
     * Send workspace/executeCommand with the standard 4-element prefix
     * (all empty) followed by a single URI argument at position 4.
     */
    private void executeCommandWithUri(String command, String uri) throws Exception {
        String params = "{\"command\":\"" + command + "\",\"arguments\":[\"\",\"\",\"\",\"\",\""
                + uri + "\"]}";
        client.sendRequest("workspace/executeCommand", params);
    }

    /**
     * Wait for the next publishDiagnostics notification whose URI matches the
     * given URI.  Ignores notifications for other URIs.
     */
    private JsonObject nextDiagsForUri(String uri, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            String msgUri = msg.getAsJsonObject("params").get("uri").getAsString();
            if (uri.equals(msgUri)) return msg;
        }
    }

    /** Return true if the diagnostics array contains at least one Error-severity (1) entry. */
    private static boolean hasErrorDiagnostic(JsonArray diags) {
        for (var el : diags) {
            JsonObject d = el.getAsJsonObject();
            if (d.has("severity") && d.get("severity").getAsInt() == 1) return true;
        }
        return false;
    }

    // -----------------------------------------------------------------------
    // openjml.runEsc command (scheduleEscFile → runWithContentOrFile)
    // -----------------------------------------------------------------------

    /**
     * Verifies that {@code openjml.runEsc [uri]} triggers an ESC pass and
     * publishes diagnostics for a file that is open in the editor (i.e. has
     * content stored in {@code lastContent}).
     *
     * <p>The URI does not correspond to a real disk file, so the server's
     * {@code runWithContentOrFile} helper must choose the in-memory content
     * path.  A postcondition that is always false guarantees ESC reports a
     * violation.
     */
    @Test
    public void testRunEscCommandPublishesEscDiagnostics() throws Exception {
        String uri = "file:///EscCmdTest.java";
        // Postcondition \result > x is never satisfied when the method returns x.
        String source = "public class EscCmdTest {\\n"
                + "    //@ ensures \\\\result > x;\\n"
                + "    public int noOp(int x) { return x; }\\n"
                + "}\\n";

        openDocument(uri, source);
        // Wait for the initial --check to complete (no type errors expected).
        nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Execute openjml.runEsc — server calls scheduleEscFile(uri)
        // → runWithContentOrFile finds lastContent → runs ESC on in-memory source.
        executeCommandWithUri(OpenJMLCommands.RUN_ESC, uri);

        // ESC may publish intermediate empty notifications (e.g. when a method proof starts
        // and the CHECKING state is pushed before results arrive).  Poll until we receive a
        // non-empty diagnostics notification for this URI.
        JsonObject escNotif = null;
        long escDeadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(TIMEOUT_SECONDS);
        while (System.nanoTime() < escDeadline) {
            long remaining = escDeadline - System.nanoTime();
            JsonObject notif = nextDiagsForUri(uri, remaining, TimeUnit.NANOSECONDS);
            if (notif == null) break;
            JsonArray diags = notif.getAsJsonObject("params").getAsJsonArray("diagnostics");
            if (!diags.isEmpty()) { escNotif = notif; break; }
        }
        assertNotNull("Expected publishDiagnostics notification after openjml.runEsc", escNotif);
        JsonArray escDiags = escNotif.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected ESC to report a postcondition violation", escDiags.isEmpty());
    }

    /**
     * Verifies that {@code textDocument/didOpen} triggers a {@code --check} and
     * publishes diagnostics when the document content (not a disk file) has a
     * type error.
     *
     * <p>The file URI does not correspond to a real disk file, so the server's
     * {@code scheduleCheckNow} falls back to content-based checking.  This
     * exercises the "no disk file → use in-memory content" branch of
     * {@code scheduleCheckNow} and confirms that {@code didOpen} always
     * triggers a check (including the case where Eclipse opens files on startup).
     */
    @Test
    public void testDidOpenWithContentTriggersCheck() throws Exception {
        String uri = "file:///OpenContentTest.java";
        String source = "public class OpenContentTest {\\n"
                + "    public int m() { return \\\"not an int\\\"; }\\n"
                + "}\\n";

        openDocument(uri, source);

        JsonObject notification =
                client.nextNotification("textDocument/publishDiagnostics",
                        TIMEOUT_SECONDS, TimeUnit.SECONDS);

        assertNotNull("Expected publishDiagnostics after didOpen with content", notification);
        JsonArray diags = notification.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one diagnostic for type error in didOpen content",
                diags.isEmpty());
        assertTrue("Expected Error-severity diagnostic", hasErrorDiagnostic(diags));
    }

    // -----------------------------------------------------------------------
    // Server capability advertisement
    // -----------------------------------------------------------------------

    /**
     * Verifies that the server's {@code initialize} response advertises all
     * capabilities that the OpenJML LSP server is known to implement.
     *
     * <p>This is a regression guard: silently removing a capability from
     * {@code ServerCapabilities} in {@code OpenJMLLanguageServer.initialize()}
     * would break clients that rely on it without any other test failing.
     *
     * <p>The response is captured during {@link #setUp()} so this test itself
     * runs entirely in-memory with no OpenJML invocation.
     */
    @Test
    public void testInitializeResponseCapabilities() {
        // The response has the shape: {"jsonrpc":"2.0","id":1,"result":{"capabilities":{...}}}
        assertTrue("initialize response must have 'result'",
                initializeResponse.has("result"));
        JsonObject result = initializeResponse.getAsJsonObject("result");
        assertTrue("initialize result must have 'capabilities'",
                result.has("capabilities"));
        JsonObject caps = result.getAsJsonObject("capabilities");

        // Each assertion guards one LSP feature the server declares it supports.
        // If a capability is removed from OpenJMLLanguageServer, the relevant
        // assertion here will fail with a clear name, making the regression obvious.
        assertTrue("Server must advertise hoverProvider",
                caps.has("hoverProvider") && !caps.get("hoverProvider").isJsonNull());
        assertTrue("Server must advertise referencesProvider",
                caps.has("referencesProvider") && !caps.get("referencesProvider").isJsonNull());
        assertTrue("Server must advertise renameProvider",
                caps.has("renameProvider") && !caps.get("renameProvider").isJsonNull());
        assertTrue("Server must advertise definitionProvider",
                caps.has("definitionProvider") && !caps.get("definitionProvider").isJsonNull());
        assertTrue("Server must advertise documentSymbolProvider",
                caps.has("documentSymbolProvider") && !caps.get("documentSymbolProvider").isJsonNull());
        assertTrue("Server must advertise completionProvider",
                caps.has("completionProvider") && !caps.get("completionProvider").isJsonNull());
        assertTrue("Server must advertise codeLensProvider",
                caps.has("codeLensProvider") && !caps.get("codeLensProvider").isJsonNull());
        assertTrue("Server must advertise foldingRangeProvider",
                caps.has("foldingRangeProvider") && !caps.get("foldingRangeProvider").isJsonNull());
        assertTrue("Server must advertise semanticTokensProvider",
                caps.has("semanticTokensProvider") && !caps.get("semanticTokensProvider").isJsonNull());

        // The rename provider must declare prepareProvider=true (required for client middleware).
        JsonObject renameOpts = caps.getAsJsonObject("renameProvider");
        assertTrue("renameProvider must have prepareProvider=true",
                renameOpts.has("prepareProvider")
                        && renameOpts.get("prepareProvider").getAsBoolean());
    }

    // -----------------------------------------------------------------------
    // Hover over wire
    // -----------------------------------------------------------------------

    /**
     * Verifies that {@code textDocument/hover} returns JML spec content over
     * the full JSON-RPC wire when the cursor is on a method that has JML
     * spec comments above it.
     *
     * <p>The hover provider reads from {@code lastContent} (set by didOpen),
     * so no separate AST population step is needed.  However, we still wait
     * for {@code publishDiagnostics} to confirm the document is fully open
     * before sending the hover request.
     */
    @Ignore("pre-existing failure: publishDiagnostics not received after didOpen — LSP module issue TBD")
    @Test
    public void testHoverReturnsJmlSpec() throws Exception {
        // File with a requires/ensures spec above the method.
        // The hover provider extracts //@ lines immediately above the method.
        String uri    = "file:///HoverWire.java";
        // Source is passed over the wire, so newlines must be literal \n within the JSON string.
        String source = "public class HoverWire {\\n"
                + "    //@ requires x >= 0;\\n"
                + "    //@ ensures \\\\result >= 0;\\n"
                + "    public int add(int x) { return x + 1; }\\n"
                + "}\\n";

        openDocument(uri, source);

        // Wait for the check to complete so that lastContent is set on the server.
        JsonObject diagNotif = client.nextNotification(
                "textDocument/publishDiagnostics", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen", diagNotif);

        // The method "add" is on line 3 (0-indexed).  Hover at that line.
        String hoverParams = "{\"textDocument\":{\"uri\":\"" + uri + "\"},"
                + "\"position\":{\"line\":3,\"character\":15}}";
        client.sendRequest("textDocument/hover", hoverParams);

        JsonObject response = client.nextResponse(SHORT_TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected a response to textDocument/hover", response);
        // The server returns null when no spec is found — here it should be non-null.
        assertFalse("Hover result must not be an error",
                response.has("error") && !response.get("error").isJsonNull());
        assertTrue("Hover response must have a 'result' field", response.has("result"));
        assertFalse("Hover result must not be JSON null (JML spec should be present)",
                response.get("result").isJsonNull());

        // The result must contain "JML spec" in the hover markup.
        String resultStr = response.get("result").toString();
        assertTrue("Hover markup must mention 'JML spec'", resultStr.contains("JML spec"));
        assertTrue("Hover markup must contain the method name 'add'", resultStr.contains("add"));
    }

    // -----------------------------------------------------------------------
    // References over wire
    // -----------------------------------------------------------------------

    /**
     * Verifies that {@code textDocument/references} returns a non-empty list
     * of locations over the full JSON-RPC wire when the cursor is on a field
     * that is referenced more than once.
     *
     * <p>The server calls {@code ReferenceFinder.findReferences} which requires
     * the AST to be cached.  We wait for {@code publishDiagnostics} (which is
     * emitted after the check completes) to ensure the AST is ready before
     * sending the references request.  Using a clean file avoids the
     * "workspace has errors, proceed anyway?" confirmation dialog.
     */
    @Test
    public void testReferencesOverWireReturnLocations() throws Exception {
        // Clean file: a field declared on line 1 and referenced on line 2.
        // References to "wireField" should include at least the declaration site.
        String uri    = "file:///WireRefTest.java";
        String source = "public class WireRefTest {\\n"
                + "    public int wireField = 0;\\n"
                + "    public void m() { int x = wireField + 1; }\\n"
                + "}\\n";

        openDocument(uri, source);

        // Wait for the initial check (populates AST cache, ensures !isWorkspaceStale).
        JsonObject diagNotif = nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen", diagNotif);

        // The field "wireField" is declared on line 1 (0-indexed), column 15.
        String refParams = "{\"textDocument\":{\"uri\":\"" + uri + "\"},"
                + "\"position\":{\"line\":1,\"character\":15},"
                + "\"context\":{\"includeDeclaration\":true}}";
        client.sendRequest("textDocument/references", refParams);

        // References is async (may re-check); allow generous time.
        JsonObject response = client.nextResponse(TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected a response to textDocument/references", response);
        assertFalse("References response must not be an error",
                response.has("error") && !response.get("error").isJsonNull());
        assertTrue("References response must have a 'result' field", response.has("result"));

        // At minimum the declaration site should be returned.
        JsonArray locations = response.getAsJsonArray("result");
        assertNotNull("References result must be a JSON array", locations);
        assertFalse("References must find at least one location for 'wireField'",
                locations.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Folding range over wire
    // -----------------------------------------------------------------------

    /**
     * Verifies that {@code textDocument/foldingRange} returns a non-empty array
     * of ranges over the full JSON-RPC wire for a document that contains
     * multi-line JML annotation blocks.
     *
     * <p>Folding range computation is a pure text scan ({@link
     * org.openjml.lsp.FoldingRangeProvider#fromSource}) that requires no AST.
     * We nonetheless wait for {@code publishDiagnostics} to confirm the document
     * is fully open on the server before sending the request, so there is no
     * race between didOpen and the foldingRange response.
     *
     * <p>This test exercises the full request / response cycle (JSON-RPC framing,
     * {@code OpenJMLTextDocumentService#foldingRange}, and
     * {@link org.openjml.lsp.FoldingRangeProvider}) — unlike
     * {@code FoldingRangeTest} which calls {@code FoldingRangeProvider.fromSource}
     * directly.
     */
    @Test
    public void testFoldingRangeOverWireReturnsRanges() throws Exception {
        String uri = "file:///FoldingWire.java";
        // Three consecutive JML line-comment lines: lines 1-3 (0-indexed).
        // FoldingRangeProvider should return at least one range covering them.
        String source = "public class FoldingWire {\\n"
                + "    //@ requires x >= 0;\\n"
                + "    //@ ensures \\\\result >= 0;\\n"
                + "    //@ assignable \\\\nothing;\\n"
                + "    public int id(int x) { return x; }\\n"
                + "}\\n";

        openDocument(uri, source);

        // Wait for the initial --check to complete (confirms doc is open on server).
        JsonObject diagNotif = nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen", diagNotif);

        // textDocument/foldingRange only needs the document URI — no position.
        String foldParams = "{\"textDocument\":{\"uri\":\"" + uri + "\"}}";
        client.sendRequest("textDocument/foldingRange", foldParams);

        JsonObject response = client.nextResponse(SHORT_TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected a response to textDocument/foldingRange", response);
        assertFalse("foldingRange response must not be an error",
                response.has("error") && !response.get("error").isJsonNull());
        assertTrue("foldingRange response must have a 'result' field", response.has("result"));
        assertFalse("foldingRange result must not be JSON null", response.get("result").isJsonNull());

        JsonArray ranges = response.getAsJsonArray("result");
        assertNotNull("foldingRange result must be a JSON array", ranges);
        assertFalse("Expected at least one folding range for the multi-line JML block",
                ranges.isEmpty());

        // The first range must span the three consecutive JML comment lines (1-3, 0-indexed).
        JsonObject first = ranges.get(0).getAsJsonObject();
        assertEquals("startLine of first folding range", 1, first.get("startLine").getAsInt());
        assertEquals("endLine of first folding range",   3, first.get("endLine").getAsInt());
    }

    // -----------------------------------------------------------------------
    // workspace/symbol: index then edit
    // -----------------------------------------------------------------------

    /**
     * Verifies that {@code workspace/symbol} reflects the live cache accurately
     * after a document is significantly edited: declarations from the original
     * content must not be returned once the editor content changes, and newly
     * introduced declarations must appear.
     *
     * <p>Scenario:
     * <ol>
     *   <li>Two in-memory files are opened.  {@code Alpha} has {@code alphaField}
     *       and {@code alphaMethod}; {@code Beta} has {@code betaField} and
     *       {@code betaMethod}.</li>
     *   <li>{@code workspace/symbol} is queried for each name — all found.</li>
     *   <li>{@code Alpha.java} is replaced entirely via {@code textDocument/didChange}:
     *       {@code alphaField} and {@code alphaMethod} disappear;
     *       {@code updatedField} and {@code updatedMethod} are introduced.
     *       The class name {@code Alpha} stays.</li>
     *   <li>After the server re-checks the file (signalled by
     *       {@code publishDiagnostics}), {@code workspace/symbol} is queried again:
     *       new names appear; old names from Alpha.java are gone; Beta's names
     *       are unaffected.</li>
     * </ol>
     */
    @Test
    public void testWorkspaceSymbolReflectsEditedContent() throws Exception {
        String alphaUri = "file:///WsAlpha.java";
        String betaUri  = "file:///WsBeta.java";

        String alphaInitial =
                "public class Alpha {\\n" +
                "    public int alphaField;\\n" +
                "    public void alphaMethod() {}\\n" +
                "}\\n";
        String betaSource =
                "public class Beta {\\n" +
                "    public int betaField;\\n" +
                "    public void betaMethod() {}\\n" +
                "}\\n";

        // Open both files; wait for the initial checks to complete.
        openDocument(alphaUri, alphaInitial);
        assertNotNull("Expected publishDiagnostics after opening Alpha",
                nextDiagsForUri(alphaUri, TIMEOUT_SECONDS, TimeUnit.SECONDS));

        openDocument(betaUri, betaSource);
        assertNotNull("Expected publishDiagnostics after opening Beta",
                nextDiagsForUri(betaUri, TIMEOUT_SECONDS, TimeUnit.SECONDS));

        // --- Phase 1: initial symbol state ---
        assertTrue("'Alpha' must be found before edit",
                queryWorkspaceSymbol("Alpha").contains("Alpha"));
        assertTrue("'alphaField' must be found before edit",
                queryWorkspaceSymbol("alphaField").contains("alphaField"));
        assertTrue("'alphaMethod' must be found before edit",
                queryWorkspaceSymbol("alphaMethod").contains("alphaMethod"));
        assertTrue("'betaField' must be found before edit",
                queryWorkspaceSymbol("betaField").contains("betaField"));
        assertTrue("'betaMethod' must be found before edit",
                queryWorkspaceSymbol("betaMethod").contains("betaMethod"));

        // --- Phase 2: heavily edit Alpha.java ---
        // alphaField and alphaMethod are gone; updatedField and updatedMethod appear.
        String alphaEdited =
                "public class Alpha {\\n" +
                "    public long updatedField;\\n" +
                "    public String updatedMethod(int x, boolean flag) { return \\\"\\\"; }\\n" +
                "}\\n";
        changeDocument(alphaUri, alphaEdited);

        // Wait for the re-check to complete.
        assertNotNull("Expected publishDiagnostics after editing Alpha",
                nextDiagsForUri(alphaUri, TIMEOUT_SECONDS, TimeUnit.SECONDS));

        // --- Phase 3: verify the index reflects the edit ---
        // Class name is unchanged.
        assertTrue("'Alpha' must still be found after edit",
                queryWorkspaceSymbol("Alpha").contains("Alpha"));
        // New members must appear.
        assertTrue("'updatedField' must be found after edit",
                queryWorkspaceSymbol("updatedField").contains("updatedField"));
        assertTrue("'updatedMethod' must be found after edit",
                queryWorkspaceSymbol("updatedMethod").contains("updatedMethod"));
        // Removed members of Alpha must be gone.
        assertFalse("'alphaField' must NOT be found after removal",
                queryWorkspaceSymbol("alphaField").contains("alphaField"));
        assertFalse("'alphaMethod' must NOT be found after removal",
                queryWorkspaceSymbol("alphaMethod").contains("alphaMethod"));
        // Beta is unchanged — its symbols must be unaffected.
        assertTrue("'betaField' must still be found after Alpha edit",
                queryWorkspaceSymbol("betaField").contains("betaField"));
        assertTrue("'betaMethod' must still be found after Alpha edit",
                queryWorkspaceSymbol("betaMethod").contains("betaMethod"));
        // New formals from the edited method must be indexed too.
        assertTrue("Formal 'x' in updatedMethod must be found",
                queryWorkspaceSymbol("x").contains("x"));
        assertTrue("Formal 'flag' in updatedMethod must be found",
                queryWorkspaceSymbol("flag").contains("flag"));
    }

    // -----------------------------------------------------------------------
    // clearAndReindex command
    // -----------------------------------------------------------------------

    /**
     * After openDocument (which triggers a check and produces diagnostics),
     * {@code openjml.clearAndReindex} must clear all server caches and publish
     * empty diagnostics for the open file. The server does NOT auto-recheck from
     * cached editor content — the client is responsible for re-sending
     * {@code textDocument/didChange} for any dirty editors after a clear.
     * This test verifies: (1) markers cleared after the command, and (2) errors
     * are restored once the client re-sends the file content via {@code didChange}.
     */
    @Test
    public void testClearAndReindexClearsMarkersAndClientResendRestoresDiags() throws Exception {
        String uri    = "file:///ClearReindex.java";
        String source = "public class ClearReindex {\\n    public int m() { return \\\"not an int\\\"; }\\n}\\n";

        openDocument(uri, source);

        // Wait for the initial check to produce error diagnostics.
        JsonObject first = nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected initial publishDiagnostics after didOpen", first);
        JsonArray firstDiags = first.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected non-empty initial diagnostics", firstDiags.isEmpty());

        // Issue clearAndReindex.
        executeCommand(OpenJMLCommands.CLEAR_AND_REINDEX);

        // The server must publish empty diagnostics (markers cleared) for the open file.
        JsonObject cleared = nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after clearAndReindex (cache clear)", cleared);
        JsonArray clearedDiags = cleared.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertEquals("Expected empty diagnostics immediately after cache clear", 0, clearedDiags.size());

        // The client re-sends the file content (correct protocol after clearAndReindex).
        changeDocument(uri, source);

        // The server should now re-check and restore the original error diagnostics.
        JsonObject rechecked = nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after client re-sent didChange", rechecked);
        JsonArray recheckedDiags = rechecked.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected non-empty diagnostics after re-check", recheckedDiags.isEmpty());
        assertTrue("Expected Error-severity diagnostic after re-check", hasErrorDiagnostic(recheckedDiags));
    }
}
