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
import java.nio.file.Path;
import java.nio.file.Paths;
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

        openDocument(uri, "");  // content ignored — server reads from disk

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

        openDocument(uri, "");  // content ignored — server reads from disk

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

    /** Send workspace/didChangeConfiguration to change the checkTriggerOn setting. */
    private void setCheckTriggerOn(String mode) throws Exception {
        String params = "{\"settings\":{\"openjml\":{\"checkTriggerOn\":\"" + mode + "\"}}}";
        client.sendNotification("workspace/didChangeConfiguration", params);
    }

    /** Return true if the diagnostics array contains at least one Error-severity (1) entry. */
    private static boolean hasErrorDiagnostic(JsonArray diags) {
        for (var el : diags) {
            JsonObject d = el.getAsJsonObject();
            if (d.has("severity") && d.get("severity").getAsInt() == 1) return true;
        }
        return false;
    }
}
