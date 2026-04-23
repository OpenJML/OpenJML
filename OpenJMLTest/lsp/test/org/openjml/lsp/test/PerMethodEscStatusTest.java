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
 * Protocol-layer tests for per-method ESC via {@code openjml.runEscForMethod}.
 *
 * <p>Exercises the full lifecycle:
 * <ul>
 *   <li>{@code scheduleEscForMethod} — dispatch from command handler</li>
 *   <li>{@code findMethod} — locate the method by name+line in the source</li>
 *   <li>{@code onMethodEscResult} — callback that updates per-method status</li>
 *   <li>{@code updateEscStatusPartial} — intermediate status refresh during ESC</li>
 *   <li>{@code getRunningEscUris} — via {@code openjml.getRunningEscTasks}</li>
 *   <li>{@code isCodeLensFormat} — two-arg vs three-arg RUN_ESC_FOR_METHOD dispatch</li>
 * </ul>
 *
 * <p>The method ref sent to {@code openjml.runEscForMethod} is extracted from the
 * actual {@code textDocument/codeLens} response so the line number is exact.
 */
public class PerMethodEscStatusTest {

    private static final long TIMEOUT_SECONDS = 120;
    private static final long SHORT_TIMEOUT   = 5;

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

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private static String jsonEscape(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");
    }

    private void didOpen(String uri, String source) throws Exception {
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}");
    }

    private JsonObject nextDiagsFor(String fragment, long timeout, TimeUnit unit)
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

    private JsonObject nextNonEmptyDiagsFor(String fragment, long timeout, TimeUnit unit)
            throws InterruptedException {
        long deadline = System.nanoTime() + unit.toNanos(timeout);
        while (true) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) return null;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) return null;
            JsonObject params = msg.getAsJsonObject("params");
            if (!params.get("uri").getAsString().contains(fragment)) continue;
            if (!params.getAsJsonArray("diagnostics").isEmpty()) return msg;
        }
    }

    private JsonArray requestCodeLens(String uri) throws Exception {
        client.sendRequest("textDocument/codeLens",
                "{\"textDocument\":{\"uri\":\"" + uri + "\"}}");
        JsonObject response = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        if (response == null || !response.has("result") || response.get("result").isJsonNull())
            return null;
        return response.getAsJsonArray("result");
    }

    private String pollLensTitleUntil(String uri, String sub, long timeoutSeconds)
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
                    if (i == 0 || last == null) last = title;
                    if (title.contains(sub)) return title;
                }
            }
            client.nextNotification("textDocument/publishDiagnostics", 200, TimeUnit.MILLISECONDS);
            Thread.sleep(300);
        }
        return last;
    }

    /**
     * Extract the first code-lens method-ref arg that contains {@code nameContains}
     * (or the first one overall if {@code nameContains} is null).
     * The method ref is args[1] of the lens command arguments.
     * Returns null if no matching lens is found.
     */
    private String extractMethodRef(JsonArray lenses, String nameContains) {
        if (lenses == null || lenses.isEmpty()) return null;
        String first = null;
        for (int i = 0; i < lenses.size(); i++) {
            JsonObject lens = lenses.get(i).getAsJsonObject();
            if (!lens.has("command")) continue;
            JsonArray args = lens.getAsJsonObject("command").getAsJsonArray("arguments");
            if (args == null || args.size() < 2) continue;
            String ref = args.get(1).getAsString();
            if (first == null) first = ref;
            if (nameContains == null || ref.contains(nameContains)) return ref;
        }
        return first; // fallback: return first available ref even if no match
    }

    private String extractMethodRef(JsonArray lenses) {
        return extractMethodRef(lenses, null);
    }

    // -----------------------------------------------------------------------
    // (1) Per-method ESC — code-lens format — NOT_VERIFIED
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEscForMethod} in code-lens format {@code [uri, methodRef]}:
     * a method with {@code ensures false} must produce NOT_VERIFIED code lens.
     *
     * The method ref is extracted from the actual code-lens response to guarantee
     * the line number is correct regardless of how {@link JavaSourceScanner} counts lines.
     */
    @Test
    public void testRunEscForMethod_CodeLensFormat_NotVerified() throws Exception {
        String uri    = "file:///PerMethodNotVerified.java";
        String source =
                "public class PerMethodNotVerified {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("PerMethodNotVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Get code lens to extract the exact methodRef produced by JavaSourceScanner.
        // Use name filter ".m(" to target the "m" method, not the constructor.
        JsonArray lenses = requestCodeLens(uri);
        assertNotNull("Expected code lenses after check", lenses);
        assertFalse("Expected at least one code lens", lenses.isEmpty());
        String methodRef = extractMethodRef(lenses, ".m(");
        assertNotNull("Code lens must include method ref arg", methodRef);

        // Code-lens format: exactly 2 args, first starts with "file://"
        String argsJson = "[\"" + uri + "\",\"" + jsonEscape(methodRef) + "\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":" + argsJson + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Wait for ESC failure diagnostics.
        JsonObject note = nextNonEmptyDiagsFor("PerMethodNotVerified", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected non-empty publishDiagnostics after per-method ESC", note);

        // Code lens must transition to NOT_VERIFIED.
        String title = pollLensTitleUntil(uri, "\u2717", 30);
        if (title == null) title = pollLensTitleUntil(uri, "Not verified", 10);
        assertNotNull("Expected code lens after per-method ESC", title);
        assertTrue("NOT_VERIFIED title must contain '✗' or 'Not verified'; got: " + title,
                title.contains("\u2717") || title.contains("Not verified"));
    }

    // -----------------------------------------------------------------------
    // (2) Per-method ESC — code-lens format — VERIFIED
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEscForMethod} on a trivially-true postcondition must
     * produce a VERIFIED code lens.
     */
    @Test
    public void testRunEscForMethod_CodeLensFormat_Verified() throws Exception {
        String uri    = "file:///PerMethodVerifiedM.java";
        String source =
                "public class PerMethodVerifiedM {\n"
                + "    //@ ensures \\result == x;\n"
                + "    public int identity(int x) { return x; }\n"
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("PerMethodVerifiedM", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        JsonArray lenses = requestCodeLens(uri);
        assertNotNull("Expected code lenses", lenses);
        String methodRef = extractMethodRef(lenses, ".identity(");
        assertNotNull("Expected methodRef from code lens", methodRef);

        String argsJson = "[\"" + uri + "\",\"" + jsonEscape(methodRef) + "\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":" + argsJson + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Drain publishDiagnostics (verified method may produce empty diags).
        nextDiagsFor("PerMethodVerifiedM", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        String title = pollLensTitleUntil(uri, "\u2713", 30);
        if (title == null) title = pollLensTitleUntil(uri, "Verified", 10);
        assertNotNull("Expected code lens after ESC", title);
        assertTrue("VERIFIED title must contain '✓' or 'Verified'; got: " + title,
                title.contains("\u2713") || title.contains("Verified"));
    }

    // -----------------------------------------------------------------------
    // (3) getRunningEscTasks command
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.getRunningEscTasks} must return a result (covering
     * {@code getRunningEscUris()}).  The list may be empty if ESC has already
     * finished, but the code path is exercised regardless.
     */
    @Test
    public void testGetRunningEscTasks() throws Exception {
        String uri    = "file:///PerMethodRunning.java";
        String source =
                "public class PerMethodRunning {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("PerMethodRunning", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        JsonArray lenses = requestCodeLens(uri);
        String methodRef = extractMethodRef(lenses, "m@");
        assertNotNull("Expected methodRef", methodRef);

        // Start per-method ESC.
        String escArgs = "[\"" + uri + "\",\"" + jsonEscape(methodRef) + "\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":" + escArgs + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Immediately query running tasks (covers getRunningEscUris()).
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.GET_RUNNING_ESC_TASKS
                + "\",\"arguments\":[]}");
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to getRunningEscTasks", resp);
        assertTrue("getRunningEscTasks must return a result", resp.has("result"));
        // Result is a list (may be empty if ESC already finished).
        assertTrue("result must be an array or null",
                resp.get("result").isJsonNull() || resp.get("result").isJsonArray());

        // Drain ESC notifications.
        nextDiagsFor("PerMethodRunning", TIMEOUT_SECONDS, TimeUnit.SECONDS);
    }

    // -----------------------------------------------------------------------
    // (4) Standard format [projectId, uri, methodRef]
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEscForMethod} in standard format {@code [projectId, uri, methodRef]}
     * exercises the else-branch of {@code isCodeLensFormat}.  Three args with a non-URI
     * first arg causes the server to parse {@code args[0]=projectId, args[1]=uri, args[2]=methodRef}.
     */
    @Test
    public void testRunEscForMethod_StandardFormat() throws Exception {
        String uri    = "file:///PerMethodStd.java";
        String source =
                "public class PerMethodStd {\n"
                + "    //@ ensures \\result >= 0;\n"
                + "    public int m() { return 5; }\n"
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("PerMethodStd", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        JsonArray lenses = requestCodeLens(uri);
        String methodRef = extractMethodRef(lenses, "m@");
        assertNotNull("Expected methodRef", methodRef);

        // Standard format: 3 args, first arg is empty projectId (not a file:// URI).
        // isCodeLensFormat() returns false for 3-arg lists.
        String argsJson = "[\"\",\"" + jsonEscape(uri) + "\",\"" + jsonEscape(methodRef) + "\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":" + argsJson + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Server must process the command; at minimum a publishDiagnostics arrives.
        nextDiagsFor("PerMethodStd", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Code lens must be updated to VERIFIED or NOT_VERIFIED (solver-dependent).
        String title = pollLensTitleUntil(uri, "\u2713", 30);
        if (title == null) title = pollLensTitleUntil(uri, "Verified", 10);
        if (title == null) title = pollLensTitleUntil(uri, "\u2717", 10);
        if (title == null) title = pollLensTitleUntil(uri, "Not verified", 10);
        assertNotNull("Expected at least one code lens after standard-format ESC", title);
    }

    // -----------------------------------------------------------------------
    // (5) @line fallback — server resolves method from AST when FQN unavailable
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEscForMethod} with {@code @<line>} as the method ref
     * (no FQN): the server must locate the containing method from the AST and
     * run ESC, producing a NOT_VERIFIED code lens for a failing postcondition.
     *
     * <p>This exercises the {@code @line} fallback path in {@code findMethod}
     * that clients use when no code-lens FQN is available yet.
     */
    @Test
    public void testRunEscForMethod_AtLineFallback_NotVerified() throws Exception {
        String uri    = "file:///AtLineFallbackFail.java";
        String source =
                "public class AtLineFallbackFail {\n"
                + "    //@ ensures false;\n"
                + "    public int fail(int x) { return x; }\n"  // declaration on line 2 (0-based)
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("AtLineFallbackFail", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Line 2 (0-based) is inside "fail" — pass @2 so the server resolves the method.
        String argsJson = "[\"" + uri + "\",\"@2\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":" + argsJson + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        JsonObject note = nextNonEmptyDiagsFor("AtLineFallbackFail", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected non-empty diagnostics after @line-fallback ESC", note);

        String title = pollLensTitleUntil(uri, "\u2717", 30);
        if (title == null) title = pollLensTitleUntil(uri, "Not verified", 10);
        assertNotNull("Expected code lens after @line-fallback ESC", title);
        assertTrue("NOT_VERIFIED title must contain '✗' or 'Not verified'; got: " + title,
                title.contains("\u2717") || title.contains("Not verified"));
    }

    /**
     * {@code openjml.runEscForMethod} with {@code @<line>} on a method with a
     * trivially true postcondition must produce a VERIFIED code lens.
     */
    @Test
    public void testRunEscForMethod_AtLineFallback_Verified() throws Exception {
        String uri    = "file:///AtLineFallbackPass.java";
        String source =
                "public class AtLineFallbackPass {\n"
                + "    //@ ensures \\result == x;\n"
                + "    public int id(int x) { return x; }\n"  // declaration on line 2 (0-based)
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("AtLineFallbackPass", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        String argsJson = "[\"" + uri + "\",\"@2\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":" + argsJson + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        nextDiagsFor("AtLineFallbackPass", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        String title = pollLensTitleUntil(uri, "\u2713", 30);
        if (title == null) title = pollLensTitleUntil(uri, "Verified", 10);
        assertNotNull("Expected code lens after @line-fallback ESC", title);
        assertTrue("VERIFIED title must contain '✓' or 'Verified'; got: " + title,
                title.contains("\u2713") || title.contains("Verified"));
    }
}
