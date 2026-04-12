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
 * Protocol-layer tests for {@code textDocument/codeLens} responses and the ESC
 * status-badge lifecycle: UNKNOWN before ESC, VERIFIED after a successful proof,
 * and NOT_VERIFIED after a proof failure.
 *
 * <p>Each test drives an in-process LSP server via {@link RawLspClient} over
 * JSON-RPC pipes.  All three status values are exercised end-to-end through the
 * full server stack, complementing the direct-API coverage in
 * {@link EscStatusTest}.
 */
public class CodeLensAndStatusTest {

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

    /**
     * Send a {@code workspace/executeCommand} request, drain its (immediate) null response,
     * and return without waiting for any async ESC result.
     */
    private void sendCommandAndDrainResponse(String command, String argsJson) throws Exception {
        String params = "{\"command\":\"" + command + "\",\"arguments\":" + argsJson + "}";
        client.sendRequest("workspace/executeCommand", params);
        // The command handler returns null immediately; ESC runs in the background.
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    /**
     * Send a {@code textDocument/codeLens} request and return the result array,
     * or null on timeout.
     */
    private JsonArray requestCodeLens(String uri) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\"}}";
        client.sendRequest("textDocument/codeLens", params);
        JsonObject response = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        if (response == null || !response.has("result")
                || response.get("result").isJsonNull()) return null;
        return response.getAsJsonArray("result");
    }

    /** Return the title string of the first code lens, or null if none. */
    private static String firstLensTitle(JsonArray lenses) {
        if (lenses == null || lenses.isEmpty()) return null;
        JsonObject lens = lenses.get(0).getAsJsonObject();
        if (!lens.has("command")) return null;
        return lens.getAsJsonObject("command").get("title").getAsString();
    }

    /**
     * Poll {@code textDocument/codeLens} until any lens title contains
     * {@code expectedSubstring} or the timeout expires.
     * Returns the matching title, or the last-seen first-lens title if none matched.
     *
     * <p>Scans all returned lenses on each poll so that a constructor lens (which
     * may appear before a method lens) does not mask the method's status.
     * The polling interval is 500 ms.
     */
    private String pollLensTitleUntil(String uri, String expectedSubstring, long timeoutSeconds)
            throws Exception {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(timeoutSeconds);
        String last = null;
        while (System.nanoTime() < deadline) {
            JsonArray lenses = requestCodeLens(uri);
            last = firstLensTitle(lenses);
            if (lenses != null) {
                for (int i = 0; i < lenses.size(); i++) {
                    JsonObject lens = lenses.get(i).getAsJsonObject();
                    if (!lens.has("command")) continue;
                    String title = lens.getAsJsonObject("command").get("title").getAsString();
                    if (title.contains(expectedSubstring)) return title;
                }
            }
            // Drain any publishDiagnostics notifications that arrived between polls.
            client.nextNotification("textDocument/publishDiagnostics", 200, TimeUnit.MILLISECONDS);
            Thread.sleep(300);
        }
        return last;
    }

    // -----------------------------------------------------------------------
    // UNKNOWN status — before any ESC run
    // -----------------------------------------------------------------------

    /**
     * After {@code textDocument/didOpen} and the resulting {@code --check}, all methods
     * must show the UNKNOWN status badge (ESC has never run).  The lens title must
     * contain the "Run ESC" indicator ({@code \u25b6} or the text "Run ESC").
     */
    @Test
    public void testCodeLensUnknownBeforeEsc() throws Exception {
        String uri    = "file:///CodeLensUnknown.java";
        String source = "public class CodeLensUnknown {\n"
                + "    public int add(int a, int b) { return a + b; }\n"
                + "}\n";
        didOpen(uri, source);
        // Drain the open-triggered --check notification.
        nextDiagsFor("CodeLensUnknown", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        JsonArray lenses = requestCodeLens(uri);
        assertNotNull("Expected code lenses for file with one method", lenses);
        assertFalse("Expected at least one code lens", lenses.isEmpty());
        String title = firstLensTitle(lenses);
        assertNotNull("Code lens must have a title", title);
        // UNKNOWN status title: "OpenJML: — ▶ Run ESC"
        assertTrue("UNKNOWN lens title must contain '▶' or 'Run ESC'; got: " + title,
                title.contains("\u25b6") || title.contains("Run ESC"));
    }

    // -----------------------------------------------------------------------
    // VERIFIED status — after successful ESC
    // -----------------------------------------------------------------------

    /**
     * After {@code openjml.runEsc} on a file with a trivially-true postcondition,
     * the code lens must show VERIFIED ({@code \u2713} or "Verified").
     */
    @Test
    public void testCodeLensVerifiedAfterEsc() throws Exception {
        String uri    = "file:///CodeLensVerified.java";
        String source = "public class CodeLensVerified {\n"
                + "    //@ ensures \\result >= 0;\n"
                + "    public int m() { return 42; }\n"
                + "}\n";
        didOpen(uri, source);
        // Drain the open-triggered --check notification.
        nextDiagsFor("CodeLensVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Run ESC on the URI (file:// prefix → uses in-memory content from lastContent).
        String argsJson = "[\"\",\"\",\"\",\"\",\"" + jsonEscape(uri) + "\"]";
        sendCommandAndDrainResponse(OpenJMLCommands.RUN_ESC, argsJson);

        // Wait for the ESC completion publishDiagnostics.
        JsonObject note = nextDiagsFor("CodeLensVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after ESC", note);

        // Poll code lenses until the status changes from UNKNOWN to VERIFIED.
        // updateEscStatus() happens before publishMerged() on the ESC thread, but there
        // can be a brief window where the codeLens handler is served before
        // methodEscStatus is visible from the LSP dispatch thread.
        // VERIFIED status title: "OpenJML: ✓ Verified ↺ Re-run"
        String title = pollLensTitleUntil(uri, "\u2713", 30);
        if (title == null) title = pollLensTitleUntil(uri, "Verified", 30);
        assertNotNull("Expected code lenses after ESC", title);
        assertTrue("VERIFIED lens title must contain '✓' or 'Verified'; got: " + title,
                title.contains("\u2713") || title.contains("Verified"));
    }

    // -----------------------------------------------------------------------
    // NOT_VERIFIED status — after ESC finds a verification failure
    // -----------------------------------------------------------------------

    /**
     * After {@code openjml.runEsc} on a method with {@code ensures false}, the
     * code lens must show NOT_VERIFIED ({@code \u2717} or "Not verified").
     */
    @Test
    public void testCodeLensNotVerifiedAfterEsc() throws Exception {
        String uri    = "file:///CodeLensNotVerified.java";
        String source = "public class CodeLensNotVerified {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        didOpen(uri, source);
        // Drain the open-triggered --check notification (no type errors for valid JML syntax).
        nextDiagsFor("CodeLensNotVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Run ESC on the URI.
        String argsJson = "[\"\",\"\",\"\",\"\",\"" + jsonEscape(uri) + "\"]";
        sendCommandAndDrainResponse(OpenJMLCommands.RUN_ESC, argsJson);

        // Wait for the ESC failure publishDiagnostics.
        JsonObject note = nextDiagsFor("CodeLensNotVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after ESC", note);
        JsonArray diags = note.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Expected at least one ESC diagnostic for 'ensures false'", diags.isEmpty());

        // Poll code lenses until the status changes from UNKNOWN to NOT_VERIFIED.
        // NOT_VERIFIED status title: "OpenJML: ✗ Not verified (N issues)"
        String title = pollLensTitleUntil(uri, "\u2717", 30);
        if (title == null) title = pollLensTitleUntil(uri, "Not verified", 30);
        assertNotNull("Expected code lenses after ESC failure", title);
        assertTrue("NOT_VERIFIED lens title must contain '✗' or 'Not verified'; got: " + title,
                title.contains("\u2717") || title.contains("Not verified"));
    }
}
