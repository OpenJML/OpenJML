package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;
import org.openjml.lsp.OpenJMLCommands;

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
public class PerMethodEscStatusTest extends ProtocolTestBase {

    // -----------------------------------------------------------------------
    // (1) Per-method ESC — NOT_VERIFIED
    // -----------------------------------------------------------------------

    /**
     * {@code openjml.runEscForMethod} format {@code [projectId, uri, methodRef]}:
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

        String argsJson = "[\"\",\"" + uri + "\",\"" + jsonEscape(methodRef) + "\"]";
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
    // (2) Per-method ESC — VERIFIED
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

        String argsJson = "[\"\",\"" + uri + "\",\"" + jsonEscape(methodRef) + "\"]";
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
        String methodRef = extractMethodRef(lenses, ".m(");
        assertNotNull("Expected methodRef", methodRef);

        // Start per-method ESC.
        String escArgs = "[\"\",\"" + uri + "\",\"" + jsonEscape(methodRef) + "\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":" + escArgs + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);

        // Immediately query running tasks (covers getRunningEscUris()).
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.GET_RUNNING_ESC_TASKS
                + "\",\"arguments\":[\"\"]}");
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
     * {@code openjml.runEscForMethod} in standard format {@code [projectId, uri, methodRef]}:
     * server parses {@code args[0]=projectId, args[1]=uri, args[2]=methodRef}.
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
        String methodRef = extractMethodRef(lenses, ".m(");
        assertNotNull("Expected methodRef", methodRef);

        // Standard format: 3 args, first arg is empty projectId.
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
        String argsJson = "[\"\",\"" + uri + "\",\"@2\"]";
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

        String argsJson = "[\"\",\"" + uri + "\",\"@2\"]";
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
