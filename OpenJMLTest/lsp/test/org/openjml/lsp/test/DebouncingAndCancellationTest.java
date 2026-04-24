package org.openjml.lsp.test;

import com.google.gson.JsonObject;
import org.junit.Test;
import org.openjml.lsp.OpenJMLCommands;

import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer tests for the check-debounce logic and ESC cancellation paths.
 *
 * <p>Each test starts a fresh in-process LSP server via {@link RawLspClient} so
 * there is no state leakage between tests.
 *
 * <h3>Coverage targets</h3>
 * <ul>
 *   <li>{@link #testRapidChangesDebounced} — exercises
 *       {@code OpenJMLTextDocumentService.debounce()} and
 *       {@code ScheduledFuture.cancel(false)}: five {@code textDocument/didChange}
 *       events sent 10 ms apart must collapse to a single {@code --check} run.</li>
 *   <li>{@link #testCancelEscWhenIdleIsHarmless} — exercises
 *       {@code cancelEsc(null)} on an empty {@code runningEscTasks} map.</li>
 *   <li>{@link #testCancelEscForSpecificUri} — exercises
 *       {@code abortEscForUri()} with no task registered for that URI.</li>
 *   <li>{@link #testEscFollowedByImmediateCancelStaysResponsive} — exercises
 *       the cancel path while an ESC task may be queued or running, verifying
 *       that the server does not deadlock or refuse further requests.</li>
 * </ul>
 */
public class DebouncingAndCancellationTest extends ProtocolTestBase {

    // -----------------------------------------------------------------------
    // Debouncing: five rapid changes → one check
    // -----------------------------------------------------------------------

    /**
     * Five {@code textDocument/didChange} events sent 10 ms apart must produce
     * exactly one {@code textDocument/publishDiagnostics}, not five.
     *
     * <p>The server's check debounce delay is 500 ms
     * ({@code OpenJMLTextDocumentService.CHECK_DEBOUNCE_MS}).  Each incoming
     * change cancels the pending {@link java.util.concurrent.ScheduledFuture} and
     * starts a new one, so only the final timer fires.  The default
     * {@code checkTriggerOn} is {@code "edit"}, so no extra configuration is
     * needed to activate debounced checks.
     */
    @Test
    public void testRapidChangesDebounced() throws Exception {
        String uri = "file:///DebounceRapid.java";
        String source0 = "public class DebounceRapid {\n"
                + "    public int add(int a, int b) { return a + b; }\n"
                + "}\n";
        didOpen(uri, source0);
        // Drain the single publishDiagnostics produced by the open-triggered --check.
        JsonObject initial = nextDiagsFor("DebounceRapid", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected publishDiagnostics after didOpen", initial);

        // Send 5 rapid changes, each 10 ms apart.  Each one rearms the 500 ms timer;
        // only the 5th timer fires and submits a single --check.
        for (int i = 1; i <= 5; i++) {
            String changed = "public class DebounceRapid {\n"
                    + "    public int v" + i + "(int a, int b) { return a + b; }\n"
                    + "}\n";
            didChange(uri, i + 1, changed);
            Thread.sleep(10);
        }

        // Wait for the single debounced check (500 ms debounce + 1–2 s check).
        JsonObject first = nextDiagsFor("DebounceRapid", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        assertNotNull("Expected exactly one publishDiagnostics after 5 rapid changes", first);

        // Allow 1.5 s more — any un-debounced extra check would appear in this window.
        JsonObject extra = nextDiagsFor("DebounceRapid", 1500, TimeUnit.MILLISECONDS);
        assertNull("Debounce must collapse 5 rapid changes into 1 --check run; "
                + "received a second publishDiagnostics", extra);
    }

    // -----------------------------------------------------------------------
    // ESC cancel: idle state
    // -----------------------------------------------------------------------

    /**
     * Sending {@code openjml.cancelEsc} with no target and no ESC running must
     * return {@code null} without throwing and leave the server responsive.
     *
     * <p>Exercises {@link org.openjml.lsp.OpenJMLTextDocumentService#cancelEsc}
     * with {@code target == null} on empty {@code runningEscTasks} and
     * {@code runningEscMethodTasks} maps.
     */
    @Test
    public void testCancelEscWhenIdleIsHarmless() throws Exception {
        String params = "{\"command\":\"" + OpenJMLCommands.CANCEL_ESC + "\",\"arguments\":[]}";
        client.sendRequest("workspace/executeCommand", params);
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to cancelEsc command", resp);
        assertTrue("cancelEsc when idle must return null result",
                resp.get("result").isJsonNull());

        // Verify the server is still responsive after the idle cancel.
        String codeLensParams = "{\"textDocument\":{\"uri\":\"file:///CancelIdleProbe.java\"}}";
        client.sendRequest("textDocument/codeLens", codeLensParams);
        JsonObject codeLensResp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must still respond to codeLens after idle cancelEsc", codeLensResp);
    }

    /**
     * Cancelling ESC for a specific URI when nothing is running for that URI must
     * be a no-op that leaves the server responsive.
     *
     * <p>Exercises {@link org.openjml.lsp.OpenJMLTextDocumentService#abortEscForUri}
     * when the URI has no entry in {@code runningEscTasks}.
     */
    @Test
    public void testCancelEscForSpecificUri() throws Exception {
        String uri = "file:///CancelSpecific.java";
        String params = "{\"command\":\"" + OpenJMLCommands.CANCEL_ESC
                + "\",\"arguments\":[\"" + uri + "\"]}";
        client.sendRequest("workspace/executeCommand", params);
        JsonObject resp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to cancelEsc", resp);
        assertTrue("cancelEsc must return null result", resp.get("result").isJsonNull());

        // Confirm the server handles a subsequent request.
        String codeLensParams = "{\"textDocument\":{\"uri\":\"" + uri + "\"}}";
        client.sendRequest("textDocument/codeLens", codeLensParams);
        assertNotNull("Server must respond to codeLens after URI-specific cancel",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
    }

    // -----------------------------------------------------------------------
    // ESC cancel: in-flight ESC
    // -----------------------------------------------------------------------

    /**
     * Sending {@code openjml.cancelEsc} immediately after dispatching
     * {@code openjml.runEsc} must not deadlock the server or cause it to refuse
     * further requests.
     *
     * <p>Whether the cancel arrives before or after the ESC task starts is a
     * race; the test does not assert on the ESC outcome.  It only verifies that
     * the server remains responsive after the sequence, exercising the
     * {@code runningEscApis} / {@code runningEscTasks} cleanup path in
     * {@link org.openjml.lsp.OpenJMLTextDocumentService#abortEscForUri}.
     */
    @Test
    public void testEscFollowedByImmediateCancelStaysResponsive() throws Exception {
        String uri    = "file:///CancelMidEsc.java";
        String source = "public class CancelMidEsc {\n"
                + "    //@ ensures \\result >= 0;\n"
                + "    public int m() { return 42; }\n"
                + "}\n";
        didOpen(uri, source);
        nextDiagsFor("CancelMidEsc", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Fire ESC: the command returns immediately; the ESC run starts asynchronously.
        String escArgs = "[\"\",\"\",\"\",\"\",\"" + jsonEscape(uri) + "\"]";
        executeCommand(OpenJMLCommands.RUN_ESC, escArgs);

        // Cancel immediately — may hit the task before or after it starts.
        String cancelParams = "{\"command\":\"" + OpenJMLCommands.CANCEL_ESC
                + "\",\"arguments\":[\"" + uri + "\"]}";
        client.sendRequest("workspace/executeCommand", cancelParams);
        JsonObject cancelResp = client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
        assertNotNull("Server must respond to cancelEsc after ESC dispatch", cancelResp);
        assertTrue("cancelEsc must return null", cancelResp.get("result").isJsonNull());

        // Drain any publishDiagnostics that arrived before or after the cancel.
        // ESC may or may not have completed — either is acceptable.
        nextDiagsFor("CancelMidEsc", 30, TimeUnit.SECONDS);

        // Verify the server still processes requests normally.
        String codeLensParams = "{\"textDocument\":{\"uri\":\"" + uri + "\"}}";
        client.sendRequest("textDocument/codeLens", codeLensParams);
        assertNotNull("Server must still respond to codeLens after ESC+cancel",
                client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS));
    }
}
