package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.openjml.lsp.OpenJMLLanguageServer;

import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for the LSP incremental-sync path through the full server stack.
 *
 * <p>Unlike {@code IncrementalSyncApplierTest} (which tests the applier in isolation),
 * these tests send JSON-RPC {@code textDocument/didChange} notifications with
 * <em>range-qualified</em> {@code contentChanges} through a live in-process server
 * and verify that the resulting {@code textDocument/publishDiagnostics} notifications
 * reflect the correctly-applied edit.  This exercises {@link org.openjml.lsp.IncrementalSyncApplier}
 * Phases 2 and 3 — the {@link org.openjml.lsp.DefinitionFinder.LineIndex}-based
 * position-to-offset conversion and the {@link StringBuilder} in-place edit — as
 * well as the full path from the LSP protocol handler through the checker and back.
 *
 * <h3>Character-position reference (0-indexed lines and characters)</h3>
 * <pre>
 *     public int m() { return "oops"; }
 * col 0   4   9   14  19      27 28  33 34 36
 * </pre>
 * <ul>
 *   <li>{@code "oops"} occupies characters 28–33 (end exclusive: 34)</li>
 *   <li>{@code 42} occupies characters 28–29 (end exclusive: 30)</li>
 *   <li>{@code "x"} occupies characters 28–30 (end exclusive: 31)</li>
 * </ul>
 *
 * <h3>Coverage targets</h3>
 * <ul>
 *   <li>{@link #testIncrementalEditFixesTypeError} — single range-qualified edit that
 *       replaces a string literal with an int literal, fixing a type error.</li>
 *   <li>{@link #testIncrementalEditIntroducesTypeError} — single range-qualified edit
 *       that introduces a type error into a previously-clean file.</li>
 *   <li>{@link #testMultipleIncrementalEditsInOneMessage} — two range-qualified edits
 *       in one {@code contentChanges} array, exercising the multi-delta
 *       {@code sb.replace()} path in {@code IncrementalSyncApplier}.</li>
 * </ul>
 */
public class IncrementalSyncProtocolTest {

    private static final long TIMEOUT_SECONDS = 120;
    private static final long SHORT_TIMEOUT   = 5;

    private static OpenJMLLanguageServer server;
    private static RawLspClient          client;

    // -----------------------------------------------------------------------
    // Shared server lifecycle
    // -----------------------------------------------------------------------

    @BeforeClass
    public static void startServer() throws Exception {
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

    @AfterClass
    public static void stopServer() {
        if (client != null) client.stop();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    private static void didOpen(String uri, String source) throws Exception {
        String params = "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}";
        client.sendNotification("textDocument/didOpen", params);
    }

    /**
     * Send a {@code textDocument/didChange} notification with a single range-qualified
     * incremental edit.  The range references the document state before this change.
     */
    private static void didChangeIncremental(String uri, int version,
            int startLine, int startChar, int endLine, int endChar,
            String newText) throws Exception {
        String range = "{\"start\":{\"line\":" + startLine + ",\"character\":" + startChar + "},"
                + "\"end\":{\"line\":" + endLine + ",\"character\":" + endChar + "}}";
        String change = "{\"range\":" + range + ",\"text\":\"" + jsonEscape(newText) + "\"}";
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\",\"version\":" + version + "},"
                + "\"contentChanges\":[" + change + "]}";
        client.sendNotification("textDocument/didChange", params);
    }

    /**
     * Send a {@code textDocument/didChange} notification with two range-qualified
     * incremental edits in one {@code contentChanges} array.  Each change's range
     * refers to the document state after all preceding changes in the same message.
     */
    private static void didChangeTwoEdits(String uri, int version,
            int sl1, int sc1, int el1, int ec1, String text1,
            int sl2, int sc2, int el2, int ec2, String text2) throws Exception {
        String range1 = "{\"start\":{\"line\":" + sl1 + ",\"character\":" + sc1 + "},"
                + "\"end\":{\"line\":" + el1 + ",\"character\":" + ec1 + "}}";
        String change1 = "{\"range\":" + range1 + ",\"text\":\"" + jsonEscape(text1) + "\"}";
        String range2 = "{\"start\":{\"line\":" + sl2 + ",\"character\":" + sc2 + "},"
                + "\"end\":{\"line\":" + el2 + ",\"character\":" + ec2 + "}}";
        String change2 = "{\"range\":" + range2 + ",\"text\":\"" + jsonEscape(text2) + "\"}";
        String params = "{\"textDocument\":{\"uri\":\"" + uri + "\",\"version\":" + version + "},"
                + "\"contentChanges\":[" + change1 + "," + change2 + "]}";
        client.sendNotification("textDocument/didChange", params);
    }

    private static JsonObject nextDiagsFor(String fragment, long timeout, TimeUnit unit)
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
    // Single incremental edit: fix type error
    // -----------------------------------------------------------------------

    /**
     * Open a file with a type error (string literal returned where int expected),
     * then send one range-qualified {@code didChange} that replaces the string literal
     * with an int literal.  Verifies that the debounced {@code --check} following the
     * incremental edit sees the corrected source and publishes empty diagnostics.
     *
     * <p>Edit: line 1 characters 28–34 ({@code "oops"}) replaced by {@code 42}.
     */
    @Test
    public void testIncrementalEditFixesTypeError() throws Exception {
        String uri = "file:///IncrSync1.java";
        // line 0: "public class IncrSync1 {"
        // line 1: "    public int m() { return "oops"; }"
        // line 2: "}"
        String source = "public class IncrSync1 {\n"
                + "    public int m() { return \"oops\"; }\n"
                + "}\n";
        didOpen(uri, source);

        // Drain the initial check — the type error must be present.
        JsonObject init = nextDiagsFor("IncrSync1", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen with type error", init);
        JsonArray initDiags = init.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Type-error source must produce diagnostics on open", initDiags.isEmpty());

        // Incremental fix: replace "oops" (line 1, chars 28–34) with 42.
        // Result: "    public int m() { return 42; }" — valid.
        didChangeIncremental(uri, 2, 1, 28, 1, 34, "42");

        JsonObject fixed = nextDiagsFor("IncrSync1", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after incremental fix", fixed);
        JsonArray fixedDiags = fixed.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("After incremental fix diagnostics must be empty", fixedDiags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Single incremental edit: introduce type error
    // -----------------------------------------------------------------------

    /**
     * Open a valid file, then send one range-qualified {@code didChange} that replaces
     * the int return value with a string literal, introducing a type error.  Verifies
     * that the resulting {@code publishDiagnostics} contains at least one error.
     *
     * <p>Edit: line 1 characters 28–30 ({@code 42}) replaced by {@code "bad"}.
     */
    @Test
    public void testIncrementalEditIntroducesTypeError() throws Exception {
        String uri = "file:///IncrSync2.java";
        String source = "public class IncrSync2 {\n"
                + "    public int m() { return 42; }\n"
                + "}\n";
        didOpen(uri, source);

        // Drain the initial check — clean file must produce no diagnostics.
        JsonObject init = nextDiagsFor("IncrSync2", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen", init);
        JsonArray initDiags = init.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("Clean file must produce empty diagnostics on open", initDiags.isEmpty());

        // Incremental break: replace 42 (line 1, chars 28–30) with the string literal "bad".
        // The Java source becomes: return "bad"; — type mismatch for int method.
        didChangeIncremental(uri, 2, 1, 28, 1, 30, "\"bad\"");

        JsonObject broken = nextDiagsFor("IncrSync2", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after introducing type error", broken);
        JsonArray brokenDiags = broken.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("File with type error must produce diagnostics", brokenDiags.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Two incremental edits in one message: multi-delta sb.replace() path
    // -----------------------------------------------------------------------

    /**
     * Send two range-qualified edits in a single {@code contentChanges} array.
     * This exercises the multi-delta {@link StringBuilder#replace} branch of
     * {@link org.openjml.lsp.IncrementalSyncApplier}: after the first edit creates
     * the {@code StringBuilder}, the second edit applies via {@code sb.replace()}
     * on the live builder.
     *
     * <p>Edits:
     * <ol>
     *   <li>Line 1, chars 28–31 ({@code "x"}) replaced by {@code 1}.</li>
     *   <li>Line 2, chars 28–31 ({@code "y"}) replaced by {@code 2}
     *       (range relative to state after edit 1; line 2 is unchanged by edit 1).</li>
     * </ol>
     * Both methods become valid; empty diagnostics are expected.
     */
    @Test
    public void testMultipleIncrementalEditsInOneMessage() throws Exception {
        String uri = "file:///IncrSync3.java";
        // line 0: "public class IncrSync3 {"
        // line 1: "    public int a() { return "x"; }"
        // line 2: "    public int b() { return "y"; }"
        // line 3: "}"
        String source = "public class IncrSync3 {\n"
                + "    public int a() { return \"x\"; }\n"
                + "    public int b() { return \"y\"; }\n"
                + "}\n";
        didOpen(uri, source);

        // Both methods have type errors initially.
        JsonObject init = nextDiagsFor("IncrSync3", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected initial publishDiagnostics", init);
        JsonArray initDiags = init.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertFalse("Both methods have type errors — diagnostics must be non-empty", initDiags.isEmpty());

        // Fix both methods in one didChange:
        //   edit 1: replace "x" (line 1, chars 28–31) with 1
        //   edit 2: replace "y" (line 2, chars 28–31) with 2
        // After edit 1, line 2 is not shifted (edit 1 is on a different line), so
        // edit 2's range {2, 28}–{2, 31} is still correct relative to the post-edit-1 state.
        didChangeTwoEdits(uri, 2,
                1, 28, 1, 31, "1",
                2, 28, 2, 31, "2");

        JsonObject fixed = nextDiagsFor("IncrSync3", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after two-edit fix", fixed);
        JsonArray fixedDiags = fixed.getAsJsonObject("params").getAsJsonArray("diagnostics");
        assertTrue("After fixing both methods diagnostics must be empty", fixedDiags.isEmpty());
    }
}
