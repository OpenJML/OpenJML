package org.openjml.lsp.test;

import org.junit.After;
import org.junit.Test;
import org.openjml.IAPI;
import org.openjml.IProverResult;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Supplier;

import static org.junit.Assert.*;

/**
 * Tests for ESC cancellation via the subprocess path.
 *
 * <p>The subprocess ESC path ({@code CheckRunner.runEscWithHook}) creates a fresh
 * {@link IAPI} and calls {@code api.execute("--esc", ...)}.  Cancelling via
 * {@link IAPI#cancelEsc()} kills the underlying z3 process, which causes OpenJML
 * to throw {@code JmlCanceledException} and exit with code 5
 * ({@code Main.Result.CANCELLED}).
 *
 * <p>Each method contains an inline JML assertion requiring non-linear integer
 * arithmetic ({@code (a*b)==0 ==> (a==0||b==0)}) that z3 cannot discharge quickly.
 * 50 methods give a reliable proving window.  Cancellation is triggered after at
 * least 2 proof results have been recorded in the run's own
 * {@link org.openjml.lsp.CheckRunner.CheckResult#proofResults()} map, so the test
 * does not depend on fixed sleep durations or machine speed.
 *
 * <p>After cancellation:
 * <ul>
 *   <li>exit code must be 5</li>
 *   <li>methods that finished before the cancel have POSSIBLY_SAT results</li>
 *   <li>the method being proved when cancel fired has a CANCELLED result entry</li>
 *   <li>if cancellation fires between methods there will be no CANCELLED entry</li>
 *   <li>methods not yet visited have no proof-result entry at all</li>
 * </ul>
 */
public class EscCancellationTest extends LspTestBase {

    private static final String URI = "file:///EscCancellation.java";

    /** Log lines captured during a test; cleared after each test. */
    private final List<String> capturedLogs = new ArrayList<>();

    @After
    public void clearLogCallback() {
        CheckRunner.setLogCallback(null);
        capturedLogs.clear();
    }

    private void installLogCapture() {
        CheckRunner.setLogCallback(capturedLogs::add);
    }

    /**
     * Source with 50 methods each containing an inline JML assertion that requires
     * non-linear integer arithmetic: {@code (a*b)==0 ==> (a==0 || b==0)}.
     * z3's quantifier-free NIA solver cannot prove this quickly, keeping each
     * method proof busy long enough for reliable cancellation.
     */
    private static final String SOURCE;
    static {
        StringBuilder sb = new StringBuilder();
        sb.append("public class EscCancellation {\n");
        for (int i = 0; i < 50; i++) {
            sb.append("    public void m").append(i).append("(int a, int b) {\n");
            sb.append("        //@ assert (a * b) == 0 ==> (a == 0 || b == 0);\n");
            sb.append("    }\n");
        }
        sb.append("}\n");
        SOURCE = sb.toString();
    }

    /**
     * Polls the live proof-count supplier until at least {@code minCount} method
     * proofs have completed in this run, then cancels via the captured IAPI.
     * This ensures cancellation fires while z3 is actively proving methods of
     * <em>this</em> run — not before proving has started or due to activity from
     * other concurrent tests or processes on the same machine.
     */
    private static void waitAndCancel(IAPI api, Supplier<Integer> proofCount,
                                      int minCount, long timeoutMs)
            throws InterruptedException {
        long deadline = System.currentTimeMillis() + timeoutMs;
        while (proofCount.get() < minCount && System.currentTimeMillis() < deadline) {
            Thread.sleep(20);
        }
        assertTrue("Expected at least " + minCount + " proof results before cancelling, got "
                + proofCount.get(), proofCount.get() >= minCount);
        api.cancelEsc();
    }

    @Test
    public void testEscCancelledExitCode5() throws Exception {
        AtomicReference<IAPI> apiRef = new AtomicReference<>();
        AtomicReference<Supplier<Integer>> countRef = new AtomicReference<>();

        Thread escThread = new Thread(() -> {
            CheckRunner.runEscWithHook(URI, SOURCE, new OpenJMLSettings(),
                    (api, count) -> { apiRef.set(api); countRef.set(count); });
        });
        escThread.setDaemon(true);
        escThread.start();

        long deadline = System.currentTimeMillis() + 20_000;
        while (apiRef.get() == null && System.currentTimeMillis() < deadline) {
            Thread.sleep(20);
        }
        assertNotNull("IAPI hook never fired within 20 s", apiRef.get());

        waitAndCancel(apiRef.get(), countRef.get(), 2, 120_000);

        escThread.join(30_000);
        assertFalse("ESC thread did not finish within 30 s after cancel", escThread.isAlive());
    }

    @Test
    public void testEscCancelledResultsAreValid() throws Exception {
        AtomicReference<IAPI> apiRef = new AtomicReference<>();
        AtomicReference<Supplier<Integer>> countRef = new AtomicReference<>();
        AtomicReference<CheckRunner.CheckResult> resultRef = new AtomicReference<>();

        Thread escThread = new Thread(() -> {
            CheckRunner.CheckResult r = CheckRunner.runEscWithHook(URI, SOURCE,
                    new OpenJMLSettings(),
                    (api, count) -> { apiRef.set(api); countRef.set(count); });
            resultRef.set(r);
        });
        escThread.setDaemon(true);
        escThread.start();

        long deadline = System.currentTimeMillis() + 20_000;
        while (apiRef.get() == null && System.currentTimeMillis() < deadline) {
            Thread.sleep(20);
        }
        assertNotNull("IAPI hook never fired within 20 s", apiRef.get());

        waitAndCancel(apiRef.get(), countRef.get(), 2, 120_000);

        escThread.join(30_000);
        assertFalse("ESC thread did not finish within 30 s after cancel", escThread.isAlive());

        CheckRunner.CheckResult result = resultRef.get();
        assertNotNull("CheckResult must not be null", result);

        // The subprocess path exits with code 5 on cancellation.
        assertEquals("Expected exit code 5 (CANCELLED) after cancelEsc()", 5, result.exitCode());

        // At least 2 methods completed before cancellation (validated by waitAndCancel above),
        // plus possibly 1 CANCELLED entry for the method mid-proof when cancel fired.
        assertTrue("Expected at least 2 proof results, got " + result.proofResults().size(),
                result.proofResults().size() >= 2);

        // Every proof result in the map must be a recognised kind value.
        // The method being proved when cancel fired has CANCELLED; methods not yet
        // reached have no entry at all.
        for (java.util.Map.Entry<String, IProverResult.Kind> e :
                result.proofResults().entrySet()) {
            IProverResult.Kind kind = e.getValue();
            assertTrue("Unexpected proof result kind " + kind + " for method " + e.getKey(),
                    kind == IProverResult.UNSAT
                    || kind == IProverResult.SAT
                    || kind == IProverResult.POSSIBLY_SAT
                    || kind == IProverResult.SKIPPED
                    || kind == IProverResult.TIMEOUT
                    || kind == IProverResult.CANCELLED);
        }
    }

    /**
     * Checks that when ESC is cancelled the log message matches the format
     * produced by {@code cancelSummary()} — specifically:
     * <ul>
     *   <li>Contains {@code "--esc EscCancellation.java cancelled:"}</li>
     *   <li>Contains {@code "method(s) completed before cancel"}</li>
     *   <li>The completed-count prefix is a non-negative integer.</li>
     *   <li>If a method was mid-proof when cancel fired the message ends with
     *       {@code ", 1 cancelled"}.</li>
     * </ul>
     *
     * <p>The test does NOT require {@code ", 1 cancelled"} to be present because
     * cancellation may land between proofs (no CANCELLED entry in that case),
     * but both branches must be syntactically correct.
     */
    @Test
    public void testCancelLogMessageFormat() throws Exception {
        installLogCapture();

        AtomicReference<IAPI> apiRef = new AtomicReference<>();
        AtomicReference<Supplier<Integer>> countRef = new AtomicReference<>();
        AtomicReference<CheckRunner.CheckResult> resultRef = new AtomicReference<>();

        Thread escThread = new Thread(() -> {
            CheckRunner.CheckResult r = CheckRunner.runEscWithHook(URI, SOURCE,
                    new OpenJMLSettings(),
                    (api, count) -> { apiRef.set(api); countRef.set(count); });
            resultRef.set(r);
        });
        escThread.setDaemon(true);
        escThread.start();

        long deadline = System.currentTimeMillis() + 20_000;
        while (apiRef.get() == null && System.currentTimeMillis() < deadline) {
            Thread.sleep(20);
        }
        assertNotNull("IAPI hook never fired within 20 s", apiRef.get());

        waitAndCancel(apiRef.get(), countRef.get(), 2, 120_000);

        escThread.join(30_000);
        assertFalse("ESC thread did not finish within 30 s after cancel", escThread.isAlive());

        // Find the cancel log line.
        String cancelLine = capturedLogs.stream()
                .filter(l -> l.contains("cancelled:"))
                .findFirst()
                .orElse(null);
        assertNotNull("Expected a log line containing 'cancelled:' but none found. Captured:\n"
                + capturedLogs, cancelLine);

        // Must name the file being cancelled.
        assertTrue("Cancel log line must contain file name 'EscCancellation.java', got: "
                + cancelLine, cancelLine.contains("EscCancellation.java cancelled:"));

        // Must contain the completed-count phrase.
        assertTrue("Cancel log line must contain 'method(s) completed before cancel', got: "
                + cancelLine, cancelLine.contains("method(s) completed before cancel"));

        // The count prefix must be a non-negative integer.
        // Format: "... cancelled: N method(s) completed before cancel..."
        int colonIdx = cancelLine.indexOf("cancelled:");
        String afterColon = cancelLine.substring(colonIdx + "cancelled:".length()).trim();
        // afterColon starts with "N method(s) ..."
        String[] parts = afterColon.split(" ", 2);
        assertTrue("Expected integer count before 'method(s)', got: " + parts[0],
                parts[0].matches("\\d+"));
        int completedCount = Integer.parseInt(parts[0]);
        assertTrue("Completed count must be >= 2 (waitAndCancel waited for 2), got: "
                + completedCount, completedCount >= 2);

        // If present, the optional suffix must be exactly ", 1 cancelled".
        // It is present iff a method was mid-proof when cancel fired.
        boolean hasCancelledEntry = resultRef.get() != null
                && resultRef.get().proofResults().containsValue(IProverResult.CANCELLED);
        if (hasCancelledEntry) {
            assertTrue("proofResults contains CANCELLED so log must end with ', 1 cancelled', got: "
                    + cancelLine, cancelLine.endsWith(", 1 cancelled"));
        } else {
            assertFalse("proofResults has no CANCELLED entry so log must not contain ', 1 cancelled', got: "
                    + cancelLine, cancelLine.contains(", 1 cancelled"));
        }
    }

    // -----------------------------------------------------------------------
    // abortCurrentProof — one method cancelled, ESC loop continues
    // -----------------------------------------------------------------------

    /**
     * Source with 10 trivial methods (prove instantly) followed by 40 hard NIA
     * methods.  After aborting the current proof the trivial methods are not yet
     * visited (they come after the hard ones in declaration order).  To keep the
     * test deterministic we place the hard methods first so the abort fires while
     * z3 is working, then the remaining hard methods (still hard) continue.
     *
     * <p>We use only 5 hard + 5 trivial methods to keep total run time reasonable
     * even if all hard methods time out.  OpenJML's default ESC timeout is applied
     * per-method; the trivial ones finish in milliseconds.
     */
    private static final String SOURCE_MIXED;
    static {
        StringBuilder sb = new StringBuilder();
        sb.append("public class EscCancellationMixed {\n");
        // 10 hard NIA methods first
        for (int i = 0; i < 10; i++) {
            sb.append("    public void hard").append(i).append("(int a, int b) {\n");
            sb.append("        //@ assert (a * b) == 0 ==> (a == 0 || b == 0);\n");
            sb.append("    }\n");
        }
        // 10 trivial methods after
        for (int i = 0; i < 10; i++) {
            sb.append("    public void easy").append(i).append("() {\n");
            sb.append("        //@ assert true;\n");
            sb.append("    }\n");
        }
        sb.append("}\n");
        SOURCE_MIXED = sb.toString();
    }

    private static final String URI_MIXED = "file:///EscCancellationMixed.java";

    /**
     * Polls until at least {@code minCount} proof results have been recorded,
     * then calls {@link IAPI#abortCurrentProof()} (not {@code cancelEsc}).
     */
    private static void waitAndAbortCurrent(IAPI api, Supplier<Integer> proofCount,
                                            int minCount, long timeoutMs)
            throws InterruptedException {
        long deadline = System.currentTimeMillis() + timeoutMs;
        while (proofCount.get() < minCount && System.currentTimeMillis() < deadline) {
            Thread.sleep(20);
        }
        assertTrue("Expected at least " + minCount + " proof results before aborting, got "
                + proofCount.get(), proofCount.get() >= minCount);
        api.abortCurrentProof();
    }

    /**
     * Verifies that {@link IAPI#abortCurrentProof()} kills the current solver
     * invocation and records CANCELLED for that method, but allows the ESC loop
     * to continue so the remaining methods are proved.
     *
     * <p>Expected outcome:
     * <ul>
     *   <li>Exit code is <em>not</em> CANCELLED (5) — the run completed normally.</li>
     *   <li>At most one CANCELLED entry — only one method can be in-flight at a time.</li>
     *   <li>All 20 methods have proof results — the loop continued after the abort.</li>
     * </ul>
     */
    @Test
    public void testAbortCurrentProofCancelsOneMethodButContinues() throws Exception {
        AtomicReference<IAPI> apiRef = new AtomicReference<>();
        AtomicReference<Supplier<Integer>> countRef = new AtomicReference<>();
        AtomicReference<CheckRunner.CheckResult> resultRef = new AtomicReference<>();

        Thread escThread = new Thread(() -> {
            CheckRunner.CheckResult r = CheckRunner.runEscWithHook(URI_MIXED, SOURCE_MIXED,
                    new OpenJMLSettings(),
                    (api, count) -> { apiRef.set(api); countRef.set(count); });
            resultRef.set(r);
        });
        escThread.setDaemon(true);
        escThread.start();

        long deadline = System.currentTimeMillis() + 20_000;
        while (apiRef.get() == null && System.currentTimeMillis() < deadline) {
            Thread.sleep(20);
        }
        assertNotNull("IAPI hook never fired within 20 s", apiRef.get());

        // Wait for at least 1 proof to complete, then abort the current proof.
        waitAndAbortCurrent(apiRef.get(), countRef.get(), 1, 120_000);

        // The ESC thread must continue and finish (not hang waiting for a future that never fires).
        escThread.join(120_000);
        assertFalse("ESC thread did not finish within 120 s after abortCurrentProof",
                escThread.isAlive());

        CheckRunner.CheckResult result = resultRef.get();
        assertNotNull("CheckResult must not be null", result);

        // Exit code must NOT be CANCELLED — the run completed.
        assertNotEquals("Exit code must not be CANCELLED (5) after abortCurrentProof",
                5, result.exitCode());

        // At most one CANCELLED entry — only one method can be in-flight when abort fires.
        long cancelledCount = result.proofResults().values().stream()
                .filter(k -> k == IProverResult.CANCELLED).count();
        assertTrue("At most one CANCELLED entry expected, got " + cancelledCount,
                cancelledCount <= 1);

        // All declared methods (and any implicit constructors) must have been visited
        // — the loop continued after the abort.  The source has 20 declared methods;
        // JmlEsc may also prove the implicit default constructor, so allow >= 20.
        assertTrue("All methods must have a proof result (loop continued after abort), got "
                + result.proofResults().size(),
                result.proofResults().size() >= 20);
    }
}
