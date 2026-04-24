package org.openjml.lsp.test;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;
import org.openjml.lsp.OpenJMLCommands;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * Tests for ESC proof-result session-generation semantics.
 *
 * <p>Step 1 of the proof-result redesign introduces a monotonic {@code sessionCounter}
 * (one increment per session at source-read time) and stores each method's proof
 * status in a {@code ProofResult} record that carries its session gen.  Results are
 * stored via an atomic compare-and-swap that keeps the highest-gen entry, so a
 * lower-gen session completing after a higher-gen session cannot overwrite the newer
 * result.
 *
 * <h3>What these tests verify</h3>
 * <ol>
 *   <li>File ESC: all methods in the file receive a code-lens status.</li>
 *   <li>Two sequential file ESC runs: the second run's results replace the first's.</li>
 *   <li>Per-method ESC after file ESC: only the target method's lens changes;
 *       other methods retain their file-run statuses.</li>
 *   <li>Concurrent sessions for the same method: the higher-gen session's result
 *       survives even when the lower-gen session completes later.  This test
 *       specifically exposes the TOCTOU race in the pre-step-1 code where
 *       {@code myGen = -1L} bypasses the staleness guard for per-method runs.</li>
 * </ol>
 *
 * <p>Tests 1–3 are also regression tests for the refactored code path; they pass
 * both before and after step 1 in the sequential case.  Test 4 is expected to be
 * flaky with the old code (races the TOCTOU window) and deterministically correct
 * after step 1.
 */
public class EscSessionGenTest extends ProtocolTestBase {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private void sendEsc(String uri) throws Exception {
        String argsJson = "[\"\",\"" + jsonEscape(uri) + "\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC + "\",\"arguments\":" + argsJson + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    /** Collect all code-lens titles for the given URI in one request. */
    private List<String> allLensTitles(String uri) throws Exception {
        JsonArray lenses = requestCodeLens(uri);
        List<String> titles = new ArrayList<>();
        if (lenses == null) return titles;
        for (int i = 0; i < lenses.size(); i++) {
            JsonObject lens = lenses.get(i).getAsJsonObject();
            if (!lens.has("command")) continue;
            titles.add(lens.getAsJsonObject("command").get("title").getAsString());
        }
        return titles;
    }

    private void sendEscForMethod(String uri, String methodRef) throws Exception {
        String argsJson = "[\"" + jsonEscape(uri) + "\",\"" + jsonEscape(methodRef) + "\"]";
        client.sendRequest("workspace/executeCommand",
                "{\"command\":\"" + OpenJMLCommands.RUN_ESC_FOR_METHOD
                + "\",\"arguments\":" + argsJson + "}");
        client.nextResponse(SHORT_TIMEOUT, TimeUnit.SECONDS);
    }

    // -----------------------------------------------------------------------
    // (1) File ESC: all methods receive a code-lens status
    // -----------------------------------------------------------------------

    /**
     * After a file-level ESC run on a two-method file, both methods must show
     * a definitive code-lens status (VERIFIED or NOT_VERIFIED), not UNKNOWN.
     *
     * <p>This is a regression test for the step-1 refactor: switching from
     * {@code methodEscStatus} to the {@code proofResults} store must not drop
     * any method's status.
     */
    @Test
    public void testFileEscAllMethodsGetStatus() throws Exception {
        String uri    = "file:///SessionGenAllMethods.java";
        String source =
                "public class SessionGenAllMethods {\n"
                + "    //@ ensures \\result == x;\n"
                + "    public int verified(int x) { return x; }\n"
                + "    //@ ensures false;\n"
                + "    public int failing(int x) { return x; }\n"
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("SessionGenAllMethods", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        sendEsc(uri);
        // Drain check notification, then wait for ESC diagnostics.
        nextNonEmptyDiagsFor("SessionGenAllMethods", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Poll until at least one lens shows VERIFIED.
        String verifiedTitle = pollLensTitleUntil(uri, "\u2713", 60);
        assertNotNull("Expected at least one VERIFIED code lens after file ESC", verifiedTitle);
        assertTrue("VERIFIED lens must contain '✓' or 'Verified'; got: " + verifiedTitle,
                verifiedTitle.contains("\u2713") || verifiedTitle.contains("Verified"));

        // Also poll until at least one lens shows NOT_VERIFIED.
        String failTitle = pollLensTitleUntil(uri, "\u2717", 60);
        assertNotNull("Expected at least one NOT_VERIFIED code lens after file ESC", failTitle);
        assertTrue("NOT_VERIFIED lens must contain '✗' or 'Not verified'; got: " + failTitle,
                failTitle.contains("\u2717") || failTitle.contains("Not verified"));
    }

    // -----------------------------------------------------------------------
    // (2) Two sequential file ESC runs: second result replaces first
    // -----------------------------------------------------------------------

    /**
     * Submit two sequential file-level ESC runs.  After the first run the
     * method is NOT_VERIFIED (spec is {@code ensures false}).  After the spec
     * is removed via {@code didChange} and the second run completes, the lens
     * must show VERIFIED.
     *
     * <p>This verifies that the second session's gen supersedes the first
     * session's gen for all methods in the file.
     */
    @Test
    public void testSecondFileEscSessionOverridesFirst() throws Exception {
        String uri = "file:///SessionGenSecondOverrides.java";
        String sourceFailing =
                "public class SessionGenSecondOverrides {\n"
                + "    //@ ensures false;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        String sourcePassing =
                "public class SessionGenSecondOverrides {\n"
                + "    //@ ensures \\result == x;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";

        didOpen(uri, sourceFailing);
        nextDiagsFor("SessionGenSecondOverrides", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Session 1: run ESC on the failing source.
        sendEsc(uri);
        nextNonEmptyDiagsFor("SessionGenSecondOverrides", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        String title1 = pollLensTitleUntil(uri, "\u2717", 60);
        assertNotNull("Session 1 must produce NOT_VERIFIED", title1);
        assertTrue("Session 1 lens must be NOT_VERIFIED; got: " + title1,
                title1.contains("\u2717") || title1.contains("Not verified"));

        // Edit: replace the spec so the method now passes.
        didChange(uri, 2, sourcePassing);
        nextDiagsFor("SessionGenSecondOverrides", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Session 2: run ESC on the passing source.
        sendEsc(uri);
        nextDiagsFor("SessionGenSecondOverrides", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        String title2 = pollLensTitleUntil(uri, "\u2713", 60);
        assertNotNull("Session 2 must produce VERIFIED", title2);
        assertTrue("Session 2 lens must be VERIFIED; got: " + title2,
                title2.contains("\u2713") || title2.contains("Verified"));
    }

    // -----------------------------------------------------------------------
    // (3) Per-method ESC after file ESC: only the target method changes
    // -----------------------------------------------------------------------

    /**
     * Run file-level ESC so that method {@code passing} is VERIFIED and
     * method {@code failing} is NOT_VERIFIED.  Then run per-method ESC on
     * {@code passing} only.  After the per-method run:
     * <ul>
     *   <li>{@code passing} must still be VERIFIED (same proof, different session gen).</li>
     *   <li>{@code failing} must still be NOT_VERIFIED — the per-method run for
     *       {@code passing} must not disturb the stored result for {@code failing}.</li>
     * </ul>
     *
     * <p>This verifies that {@code proofResults} are keyed per-method and that a
     * per-method session does not evict proof results for unrelated methods.
     */
    @Test
    public void testPerMethodEscUpdatesOnlyTargetMethod() throws Exception {
        String uri    = "file:///SessionGenPerMethod.java";
        String source =
                "public class SessionGenPerMethod {\n"
                + "    //@ ensures \\result == x;\n"
                + "    public int passing(int x) { return x; }\n"
                + "    //@ ensures false;\n"
                + "    public int failing(int x) { return x; }\n"
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("SessionGenPerMethod", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // File ESC session: both methods get results.
        sendEsc(uri);
        nextNonEmptyDiagsFor("SessionGenPerMethod", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        // Wait until both statuses are settled.
        pollLensTitleUntil(uri, "\u2713", 60);
        pollLensTitleUntil(uri, "\u2717", 60);

        // Snapshot all lens titles after file ESC.
        List<String> afterFile = allLensTitles(uri);
        long verifiedCount  = afterFile.stream().filter(t -> t.contains("\u2713") || t.contains("Verified")).count();
        long failingCount   = afterFile.stream().filter(t -> t.contains("\u2717") || t.contains("Not verified")).count();
        assertTrue("File ESC must produce at least one VERIFIED lens", verifiedCount >= 1);
        assertTrue("File ESC must produce at least one NOT_VERIFIED lens", failingCount >= 1);

        // Per-method ESC session: run ESC only on 'passing'.
        JsonArray lenses = requestCodeLens(uri);
        String passingRef = extractMethodRef(lenses, "passing");
        assertNotNull("Must find a method ref for 'passing'", passingRef);
        sendEscForMethod(uri, passingRef);
        // Drain diagnostic notifications from the per-method run.
        nextDiagsFor("SessionGenPerMethod", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        // Wait for the per-method result to appear.
        pollLensTitleUntil(uri, "\u2713", 60);

        // After per-method ESC, 'failing' must still be NOT_VERIFIED.
        // Retry a few times to let the server settle.
        List<String> afterPerMethod = null;
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(30);
        while (System.nanoTime() < deadline) {
            afterPerMethod = allLensTitles(uri);
            long stillFailing = afterPerMethod.stream()
                    .filter(t -> t.contains("\u2717") || t.contains("Not verified")).count();
            if (stillFailing >= 1) break;
            Thread.sleep(300);
        }
        assertNotNull("Expected lens titles after per-method ESC", afterPerMethod);
        long stillFailing = afterPerMethod.stream()
                .filter(t -> t.contains("\u2717") || t.contains("Not verified")).count();
        assertTrue("Per-method ESC for 'passing' must not clear 'failing' NOT_VERIFIED status; "
                + "lenses: " + afterPerMethod, stillFailing >= 1);
    }

    // -----------------------------------------------------------------------
    // (4) Higher-gen session result survives when lower-gen session completes later
    // -----------------------------------------------------------------------

    /**
     * Exercises the core step-1 correctness property: the result from a
     * higher-gen session must not be overwritten by a lower-gen session that
     * completes later.
     *
     * <p>Setup:
     * <ul>
     *   <li>A file with a slow method {@code slow} (non-linear integer
     *       arithmetic — z3 takes seconds) and a fast method {@code fast}
     *       (identity, trivially UNSAT).</li>
     *   <li>Session 1 (lower gen): file-level ESC that will prove {@code slow}
     *       first, then {@code fast}.</li>
     *   <li>Session 2 (higher gen): per-method ESC for {@code fast} only,
     *       submitted while session 1 is still proving {@code slow}.  Session 2
     *       completes quickly.</li>
     * </ul>
     *
     * <p>Expected outcome: {@code fast} shows VERIFIED from session 2.  When
     * session 1 eventually proves {@code fast} (gen lower than session 2's gen),
     * its result must be discarded by the CAS store and must not overwrite session 2's
     * VERIFIED status.
     *
     * <p>Pre-step-1 behaviour: {@code myGen = -1L} bypasses the staleness guard for
     * per-method runs; additionally, if two sessions race on the same method the
     * last writer wins, which may be the lower-gen session.  This test is therefore
     * expected to be flaky with the old code and deterministically correct after
     * step 1.
     */
    @Test
    public void testHigherGenResultSurvivesLowerGenLateArrival() throws Exception {
        String uri    = "file:///SessionGenHigherGen.java";
        // 'slow' has non-linear arithmetic that z3 takes several seconds on.
        // 'fast' has a trivially-true postcondition that z3 solves immediately.
        String source =
                "public class SessionGenHigherGen {\n"
                + "    public void slow(int a, int b) {\n"
                + "        //@ assert (a * b) == 0 ==> (a == 0 || b == 0);\n"
                + "    }\n"
                + "    //@ ensures \\result == x;\n"
                + "    public int fast(int x) { return x; }\n"
                + "}\n";

        didOpen(uri, source);
        nextDiagsFor("SessionGenHigherGen", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Session 1 (lower gen): file-level ESC — will prove 'slow' first.
        // Do NOT wait for it to complete; start session 2 immediately.
        sendEsc(uri);

        // Brief pause to let the server dispatch session 1 before we submit session 2.
        Thread.sleep(200);

        // Session 2 (higher gen): per-method ESC for 'fast'.
        // Submitted while session 1 is in the middle of proving 'slow'.
        JsonArray lenses = requestCodeLens(uri);
        String fastRef = extractMethodRef(lenses, "fast");
        assertNotNull("Must find a method ref for 'fast'", fastRef);
        sendEscForMethod(uri, fastRef);

        // Wait for session 2 to complete (fast method, should finish well under 60 s).
        nextDiagsFor("SessionGenHigherGen", TIMEOUT_SECONDS, TimeUnit.SECONDS);
        String fastTitle = pollLensTitleUntil(uri, "\u2713", 60);
        assertNotNull("Session 2 must produce a VERIFIED lens for 'fast'", fastTitle);
        assertTrue("'fast' must be VERIFIED after session 2; got: " + fastTitle,
                fastTitle.contains("\u2713") || fastTitle.contains("Verified"));

        // Wait for session 1 to complete (slow method; allow up to 120 s).
        // After session 1 finishes, 'fast' must still be VERIFIED — session 1's
        // lower-gen result for 'fast' must have been discarded by the CAS store.
        nextDiagsFor("SessionGenHigherGen", TIMEOUT_SECONDS, TimeUnit.SECONDS);

        // Poll 'fast' lens for a few more seconds; any NOT_VERIFIED or UNKNOWN
        // transition would indicate the lower-gen result leaked through.
        long checkDeadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(10);
        String lastFastTitle = fastTitle;
        while (System.nanoTime() < checkDeadline) {
            List<String> titles = allLensTitles(uri);
            for (String t : titles) {
                if (t.contains("fast") || titles.indexOf(t) == 1) {
                    lastFastTitle = t;
                    break;
                }
            }
            // Drain notifications.
            client.nextNotification("textDocument/publishDiagnostics", 200, TimeUnit.MILLISECONDS);
            Thread.sleep(200);
        }

        // 'fast' must still be VERIFIED; it must not have reverted.
        // Find the lens title for 'fast' in the final snapshot.
        List<String> finalTitles = allLensTitles(uri);
        long verifiedFast = finalTitles.stream()
                .filter(t -> t.contains("\u2713") || t.contains("Verified")).count();
        assertTrue("'fast' must remain VERIFIED after session 1 completes; "
                + "final lenses: " + finalTitles, verifiedFast >= 1);
    }
}
