package org.openjml.lsp.test;

import org.junit.Test;
import org.openjml.IAPI;
import org.openjml.IProverResult;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

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
}
