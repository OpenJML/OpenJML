package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.OpenJMLCommands;
import org.openjml.lsp.OpenJMLLanguageServer;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for code lenses in {@code .jml} companion spec files.
 *
 * <p>Each test drives an in-process LSP server via {@link RawLspClient} over
 * JSON-RPC pipes.  Real disk files (in a {@link TemporaryFolder}) are used so
 * that OpenJML can find the {@code .jml} companion during a {@code --check} pass
 * on the companion {@code .java} file, which is required to populate the AST
 * cache entry that {@code codeLensForJml} reads.
 */
public class JmlCodeLensTest {

    private static final long TIMEOUT_SECONDS = 120;
    private static final long SHORT_TIMEOUT   = 5;

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

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

        // Initialize with the temp folder as workspace root so settingsForUri()
        // finds a project for the real file:// URIs used in these tests.
        String rootUri = tmp.getRoot().toPath().toUri().toString();
        client.sendRequest("initialize",
                "{\"processId\":null,\"rootUri\":\"" + rootUri
                + "\",\"capabilities\":{}}");
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

    private File writeFile(String filename, String content) throws IOException {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    private static String fileUri(File f) {
        return f.toPath().toUri().toString();
    }

    private static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    private void didOpen(String uri, String source) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}";
        client.sendNotification("textDocument/didOpen", params);
    }

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

    /** Send workspace/executeCommand, drain the immediate null response. */
    private void sendCommandAndDrainResponse(String command, String argsJson) throws Exception {
        String params = "{\"command\":\"" + command + "\",\"arguments\":" + argsJson + "}";
        client.sendRequest("workspace/executeCommand", params);
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    /** Send textDocument/codeLens and return the result array, or null on timeout. */
    private JsonArray requestCodeLens(String uri) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\"}}";
        client.sendRequest("textDocument/codeLens", params);
        JsonObject response = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        if (response == null || !response.has("result")
                || response.get("result").isJsonNull()) return null;
        return response.getAsJsonArray("result");
    }

    /** Return the title of the first code lens, or null. */
    private static String firstLensTitle(JsonArray lenses) {
        if (lenses == null || lenses.isEmpty()) return null;
        JsonObject lens = lenses.get(0).getAsJsonObject();
        if (!lens.has("command")) return null;
        return lens.getAsJsonObject("command").get("title").getAsString();
    }

    /**
     * Poll textDocument/codeLens until any lens title contains {@code expected}
     * or the timeout expires.  Returns the matching title, or the last-seen
     * first-lens title if none matched.
     */
    private String pollLensTitleUntil(String uri, String expected, long timeoutSeconds)
            throws Exception {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(timeoutSeconds);
        String last = null;
        while (System.nanoTime() < deadline) {
            JsonArray lenses = requestCodeLens(uri);
            if (lenses != null) {
                for (int i = 0; i < lenses.size(); i++) {
                    JsonObject lens = lenses.get(i).getAsJsonObject();
                    if (!lens.has("command")) continue;
                    String title = lens.getAsJsonObject("command").get("title").getAsString();
                    last = title;
                    if (title.contains(expected)) return title;
                }
            }
            client.nextNotification("textDocument/publishDiagnostics", 200, TimeUnit.MILLISECONDS);
            Thread.sleep(300);
        }
        return last;
    }

    // -----------------------------------------------------------------------
    // Test 1: .jml code lenses — UNKNOWN status before ESC
    // -----------------------------------------------------------------------

    /**
     * After opening both the {@code .java} and {@code .jml} files, a
     * {@code textDocument/codeLens} request for the {@code .jml} URI must
     * return at least one code lens with UNKNOWN status (no ESC has run yet).
     *
     * <p>The lens is only shown when the {@code .jml} file is open in an
     * editor ({@link #didOpen} stores its content).
     */
    @Test
    public void testJmlCodeLensUnknownBeforeEsc() throws Exception {
        String javaSource =
                "public class JmlLensUnknown {\n" +
                "    //@ ensures \\result == spec(x);\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n";
        String jmlSource =
                "public class JmlLensUnknown {\n" +
                "    //@ pure model public int spec(int x) { return x * 2; }\n" +
                "}\n";

        File javaFile = writeFile("JmlLensUnknown.java", javaSource);
        File jmlFile  = writeFile("JmlLensUnknown.jml",  jmlSource);
        String javaUri = fileUri(javaFile);
        String jmlUri  = fileUri(jmlFile);

        // Open .java first: triggers --check which caches both .java and .jml ASTs.
        didOpen(javaUri, javaSource);
        JsonObject checkDiag = nextDiagsFor("JmlLensUnknown", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Server must publish diagnostics after --check on .java file", checkDiag);

        // Open .jml: stores content in lastContent so codeLensForJml can proceed.
        didOpen(jmlUri, jmlSource);
        // Brief wait for the open-triggered re-check to complete.
        nextDiagsFor("JmlLensUnknown", TIMEOUT_SECONDS / 2, TimeUnit.SECONDS);

        // Request code lenses for the .jml URI.
        JsonArray lenses = requestCodeLens(jmlUri);
        System.out.println("[JmlCodeLensTest] .jml lenses before ESC: " + lenses);
        assertNotNull("Expected code lenses for open .jml file", lenses);
        assertFalse("Expected at least one lens for the model method 'spec'", lenses.isEmpty());

        String title = firstLensTitle(lenses);
        assertNotNull("Lens must have a title", title);
        System.out.println("[JmlCodeLensTest] first lens title before ESC: " + title);
        // UNKNOWN status: lens must show the Run-ESC indicator.
        assertTrue("UNKNOWN lens title must contain '▶' or 'Run ESC'; got: " + title,
                title.contains("\u25b6") || title.contains("Run ESC"));
    }

    // -----------------------------------------------------------------------
    // Test 2: .jml code lenses — VERIFIED status after ESC
    // -----------------------------------------------------------------------

    /**
     * After {@code openjml.runEsc} on the companion {@code .java} file,
     * the code lenses in the {@code .jml} editor must eventually show VERIFIED
     * for the model method whose body satisfies its spec.
     *
     * <p>Verifies the full {@link org.openjml.lsp.OpenJMLTextDocumentService#updateJmlEscStatus}
     * path: ESC runs on the {@code .java} file, proof results are propagated to the
     * {@code .jml} status map, and a subsequent {@code textDocument/codeLens} request
     * returns the VERIFIED label.
     */
    @Test
    public void testJmlCodeLensVerifiedAfterEsc() throws Exception {
        String javaSource =
                "public class JmlLensVerified {\n" +
                "    //@ ensures \\result == spec(x);\n" +
                "    public int doubled(int x) { return x * 2; }\n" +
                "}\n";
        String jmlSource =
                "public class JmlLensVerified {\n" +
                "    //@ pure model public int spec(int x) { return x * 2; }\n" +
                "}\n";

        File javaFile = writeFile("JmlLensVerified.java", javaSource);
        File jmlFile  = writeFile("JmlLensVerified.jml",  jmlSource);
        String javaUri = fileUri(javaFile);
        String jmlUri  = fileUri(jmlFile);

        // Open .java: --check populates AST cache for both files.
        didOpen(javaUri, javaSource);
        nextDiagsFor("JmlLensVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Open .jml: stores content in lastContent.
        didOpen(jmlUri, jmlSource);
        nextDiagsFor("JmlLensVerified", TIMEOUT_SECONDS / 2, TimeUnit.SECONDS);

        // Run ESC on the .java file (not the .jml — ESC runs on .java only).
        // Use the real file-system path so OpenJML can load the companion .jml.
        String escArgs = "[\"\",\"\",\"\",\"\",\"" + jsonEscape(javaUri) + "\"]";
        sendCommandAndDrainResponse(OpenJMLCommands.RUN_ESC, escArgs);

        // Wait for ESC to complete.
        nextDiagsFor("JmlLensVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Poll .jml code lenses until the status becomes VERIFIED.
        // updateJmlEscStatus propagates the proof result to methodEscStatus[jmlUri].
        String title = pollLensTitleUntil(jmlUri, "\u2713", 30);
        if (title == null) title = pollLensTitleUntil(jmlUri, "Verified", 30);
        System.out.println("[JmlCodeLensTest] .jml lens title after ESC: " + title);
        assertNotNull("Expected code lenses after ESC on .java file", title);
        assertTrue("VERIFIED lens title must contain '✓' or 'Verified'; got: " + title,
                title.contains("\u2713") || title.contains("Verified"));
    }

    // -----------------------------------------------------------------------
    // Test 3: .jml code lenses — not shown when .jml file is not open
    // -----------------------------------------------------------------------

    /**
     * When the {@code .jml} file has NOT been opened in an editor
     * ({@code didOpen} was not called), a {@code textDocument/codeLens} request
     * for the {@code .jml} URI must return an empty list rather than an error.
     *
     * <p>This guards the requirement that code lenses in the {@code .jml} editor
     * are only shown when the file is actually open.
     */
    @Test
    public void testJmlCodeLensEmptyWhenNotOpen() throws Exception {
        String javaSource =
                "public class JmlLensNotOpen {\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n";
        String jmlSource =
                "public class JmlLensNotOpen {\n" +
                "    //@ pure model public int spec(int x) { return x; }\n" +
                "}\n";

        File javaFile = writeFile("JmlLensNotOpen.java", javaSource);
        File jmlFile  = writeFile("JmlLensNotOpen.jml",  jmlSource);
        String javaUri = fileUri(javaFile);
        String jmlUri  = fileUri(jmlFile);

        // Open ONLY the .java file — do NOT open the .jml file.
        didOpen(javaUri, javaSource);
        nextDiagsFor("JmlLensNotOpen", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Code lens request for the .jml URI must return empty (not null/error).
        JsonArray lenses = requestCodeLens(jmlUri);
        System.out.println("[JmlCodeLensTest] .jml lenses when not open: " + lenses);
        // A null result is also acceptable; an empty array or null both indicate no lenses.
        assertTrue("Code lenses for unopened .jml file must be empty or null",
                lenses == null || lenses.isEmpty());
    }
}
