package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.lsp.OpenJMLCommands;

import java.io.File;
import java.io.FileWriter;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Protocol-layer test that reproduces the "Clear All Markers then re-ESC"
 * workflow that Eclipse uses.
 *
 * <p>The scenario:
 * <ol>
 *   <li>Open two files each with one failing and one verified method.</li>
 *   <li>Run {@code openjml.runEsc} on both (OS paths) and wait until both
 *       files have received their error ESC diagnostics and the run is idle.</li>
 *   <li>Send {@code openjml.clearMarkers} — verify the server publishes empty
 *       diagnostic lists for both files.</li>
 *   <li>Run {@code openjml.runEsc} again on the same paths.</li>
 *   <li>Assert that diagnostics during the second run are not doubled — each
 *       file should have exactly 1 ESC error, not 2 (which would indicate
 *       stale {@code proofResults} from the first run leaking through).</li>
 * </ol>
 *
 * <p>Specifically the test verifies that after a clear the server does not
 * accumulate old proof results alongside new ones.
 */
public class ClearAndReescTest extends ProtocolTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    @Before
    @Override
    public void setUp() throws Exception {
        startServer();
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private File writeJava(String filename, String content) throws Exception {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }

    private void didOpenAndDrainCheck(String uri, String source) throws Exception {
        client.sendNotification("textDocument/didOpen",
                "{\"textDocument\":{\"uri\":\"" + uri
                + "\",\"languageId\":\"java\",\"version\":1,"
                + "\"text\":\"" + jsonEscape(source) + "\"}}");
        nextDiagsForUri(uri, TIMEOUT_SECONDS, TimeUnit.SECONDS);
    }

    private static int countEscErrors(JsonArray diags) {
        int n = 0;
        for (int i = 0; i < diags.size(); i++) {
            JsonObject d = diags.get(i).getAsJsonObject();
            if (d.has("source")
                    && org.openjml.lsp.DiagnosticConverter.SOURCE_ESC.equals(d.get("source").getAsString())
                    && d.has("severity") && d.get("severity").getAsInt() == 1 /* Error */)
                n++;
        }
        return n;
    }

    /**
     * Drains publishDiagnostics until both A and B have received ERROR-severity
     * ESC diagnostics, then idles for {@code idleSeconds} with no further
     * notifications for either URI to ensure the ESC run has fully settled.
     */
    private void drainEscErrorsForBothUris(String uriA, String uriB,
            int idleSeconds) throws InterruptedException {
        long deadline = System.nanoTime() + TIMEOUT_SECONDS * 1_000_000_000L;
        boolean errorA = false, errorB = false;
        while (!(errorA && errorB)) {
            long remaining = deadline - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            String uri = params.get("uri").getAsString();
            JsonArray diags = params.getAsJsonArray("diagnostics");
            if (uri.equals(uriA) && hasEscError(diags)) errorA = true;
            if (uri.equals(uriB) && hasEscError(diags)) errorB = true;
        }
        assertTrue("First ESC run must produce error diags for A", errorA);
        assertTrue("First ESC run must produce error diags for B", errorB);

        // Drain any remaining notifications until idle for idleSeconds.
        // This ensures the ESC run has fully completed (end-of-run publishMerged calls done)
        // before we send clearMarkers, so there is no race with a still-running ESC.
        while (true) {
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", idleSeconds, TimeUnit.SECONDS);
            if (msg == null) break; // idle timeout — run is done
        }
    }

    private void sendRunEsc(String pathA, String pathB) throws Exception {
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC
                + "\",\"arguments\":[\"\",\"" + jsonEscape(pathA)
                + "\",\"" + jsonEscape(pathB) + "\"]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    private void sendClearMarkers() throws Exception {
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"openjml.clearMarkers\",\"arguments\":[]}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    // -----------------------------------------------------------------------
    // Test
    // -----------------------------------------------------------------------

    /**
     * Runs ESC on two failing files, waits for both to receive their error
     * diagnostics and the run to go idle, clears all markers, runs ESC again,
     * and verifies that:
     * <ul>
     *   <li>After the clear, the server publishes empty diagnostics for both files.</li>
     *   <li>During the second ESC run, each file's first error notification
     *       contains exactly 1 ESC error — not 2, which would indicate stale
     *       proof results from the first run were merged with new ones.</li>
     *   <li>The final notification for each file contains exactly 1 ESC error.</li>
     * </ul>
     */
    @Test
    public void testClearThenReEscDoesNotDuplicateMarkers() throws Exception {
        // Each file has exactly one failing method and one trivially verified constructor.
        String srcA =
                "public class ClearReEscA {\n"
                + "    //@ ensures false;\n"
                + "    public int bad(int x) { return x; }\n"
                + "}\n";
        String srcB =
                "public class ClearReEscB {\n"
                + "    //@ ensures false;\n"
                + "    public int bad(int x) { return x; }\n"
                + "}\n";

        File fA   = writeJava("ClearReEscA.java", srcA);
        File fB   = writeJava("ClearReEscB.java", srcB);
        String uriA  = fA.toPath().toUri().toString();
        String uriB  = fB.toPath().toUri().toString();
        String pathA = fA.getAbsolutePath();
        String pathB = fB.getAbsolutePath();

        didOpenAndDrainCheck(uriA, srcA);
        didOpenAndDrainCheck(uriB, srcB);

        // ---- First ESC run ------------------------------------------------
        sendRunEsc(pathA, pathB);
        // Wait until both files have received error ESC diags, then idle for
        // 3 s to ensure the end-of-run publishMerged calls have all completed
        // before we send clearMarkers.  Without this idle wait the second runEsc
        // arrives while the first run's B.bad proof is still in progress, which
        // cancels the first run mid-flight and leaves partial state behind.
        drainEscErrorsForBothUris(uriA, uriB, 3);

        // ---- Clear all markers --------------------------------------------
        sendClearMarkers();

        // The server must publish empty diagnostics for both files.
        boolean clearedA = false, clearedB = false;
        long clearDeadline = System.nanoTime() + SHORT_TIMEOUT * 1_000_000_000L;
        while (!(clearedA && clearedB)) {
            long remaining = clearDeadline - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            String uri = params.get("uri").getAsString();
            if (params.getAsJsonArray("diagnostics").isEmpty()) {
                if (uri.equals(uriA)) clearedA = true;
                if (uri.equals(uriB)) clearedB = true;
            }
        }
        assertTrue("Server must publish empty diags for A after clearMarkers", clearedA);
        assertTrue("Server must publish empty diags for B after clearMarkers", clearedB);

        // ---- Second ESC run -----------------------------------------------
        sendRunEsc(pathA, pathB);

        // Collect the first error-containing ESC notification for each file.
        // Each file has exactly one failing method (bad), so each notification
        // that contains errors should have exactly 1.  If the server incorrectly
        // merged old proofResults with new ones the count would be 2.
        int firstErrA = -1, firstErrB = -1;
        long escDeadline = System.nanoTime() + TIMEOUT_SECONDS * 1_000_000_000L;
        while (firstErrA < 0 || firstErrB < 0) {
            long remaining = escDeadline - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            String uri = params.get("uri").getAsString();
            JsonArray diags = params.getAsJsonArray("diagnostics");
            if (!hasEscError(diags)) continue; // skip hint-only or empty notifications
            int errors = countEscErrors(diags);
            if (uri.equals(uriA) && firstErrA < 0) firstErrA = errors;
            if (uri.equals(uriB) && firstErrB < 0) firstErrB = errors;
        }

        assertTrue("Second ESC must produce ESC errors for A", firstErrA >= 0);
        assertTrue("Second ESC must produce ESC errors for B", firstErrB >= 0);

        // The first error notification for each file must carry exactly 1 error.
        // Count 2 would mean stale proofResults from before the clear leaked through.
        assertEquals(
                "First error notification for A must have exactly 1 error (not doubled from stale cache)",
                1, firstErrA);
        assertEquals(
                "First error notification for B must have exactly 1 error (not doubled from stale cache)",
                1, firstErrB);

        // Drain remaining notifications and verify the final count stays at 1.
        int lastErrA = firstErrA, lastErrB = firstErrB;
        long finalDeadline = System.nanoTime() + TIMEOUT_SECONDS * 1_000_000_000L;
        while (true) {
            long remaining = finalDeadline - System.nanoTime();
            if (remaining <= 0) break;
            JsonObject msg = client.nextNotification(
                    "textDocument/publishDiagnostics", remaining, TimeUnit.NANOSECONDS);
            if (msg == null) break;
            JsonObject params = msg.getAsJsonObject("params");
            String uri = params.get("uri").getAsString();
            JsonArray diags = params.getAsJsonArray("diagnostics");
            if (!hasEscDiag(diags)) continue;
            int errors = countEscErrors(diags);
            if (uri.equals(uriA)) lastErrA = errors;
            if (uri.equals(uriB)) lastErrB = errors;
        }

        assertEquals("Final ESC notification for A must have exactly 1 error", 1, lastErrA);
        assertEquals("Final ESC notification for B must have exactly 1 error", 1, lastErrB);
    }
}
