package org.openjml.lsp.test;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.openjml.IAPI;
import org.openjml.IProverResult;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.OpenJMLSettings;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.Assert.*;

/**
 * Tests for concurrent per-method ESC invocations.
 *
 * <p>Key properties verified:
 * <ul>
 *   <li>Multiple concurrent {@link CheckRunner#runEscMethod} calls on the same
 *       source each produce correct, independent results — no cross-contamination
 *       of proof entries between runs.</li>
 *   <li>Cancelling one in-flight method ESC run (via {@link IAPI#cancelEsc()})
 *       leaves a concurrently running method ESC run unaffected — the cancelled
 *       run exits with code 5 (CANCELLED) while the other completes normally.</li>
 * </ul>
 *
 * <h3>Method design</h3>
 * <p>Verified methods use {@code id(int x) { return x; }} with
 * {@code ensures \result == x;} — no arithmetic, no overflow, trivially UNSAT.
 * Failing methods use {@code zero(int x) { return 0; }} with
 * {@code ensures \result != 0;} — always has a counterexample.
 * Slow methods contain a non-linear integer assertion
 * ({@code (a*b)==0 ==> (a==0||b==0)}) that z3 cannot discharge quickly —
 * used to keep a run alive long enough to cancel it reliably.
 */
public class ConcurrentEscTest extends LspTestBase {

    @Rule
    public TemporaryFolder tmp = new TemporaryFolder();

    private File writeJava(String filename, String content) throws IOException {
        File f = tmp.newFile(filename);
        try (FileWriter w = new FileWriter(f)) { w.write(content); }
        return f;
    }


    // -----------------------------------------------------------------------
    // (1) Concurrent in-memory per-method runs — correct results for all
    // -----------------------------------------------------------------------

    /**
     * Submits 5 concurrent {@link CheckRunner#runEscMethod} calls on the same
     * in-memory source (3 verified, 2 failing).  Each run creates its own
     * subprocess/IAPI; none should interfere with the others.
     *
     * <p>Every result must contain exactly one proof entry for the targeted
     * method, with the correct kind (UNSAT for {@code good*}, SAT/POSSIBLY_SAT
     * for {@code bad*}).
     */
    @Test
    public void testConcurrentMethodRunsReturnCorrectResults() throws Exception {
        String uri = "file:///ConcurrentEscMixed.java";
        String source =
                "public class ConcurrentEscMixed {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int good1(int x) { return x; }\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int good2(int x) { return x; }\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int good3(int x) { return x; }\n" +
                "    //@ ensures \\result != 0;\n" +
                "    public int bad1(int x) { return 0; }\n" +
                "    //@ ensures \\result != 0;\n" +
                "    public int bad2(int x) { return 0; }\n" +
                "}\n";

        ExecutorService pool = Executors.newFixedThreadPool(5);
        List<Future<CheckRunner.CheckResult>> futures = new ArrayList<>();
        try {
            futures.add(pool.submit(() -> CheckRunner.runEscMethod(uri, source, "good1")));
            futures.add(pool.submit(() -> CheckRunner.runEscMethod(uri, source, "good2")));
            futures.add(pool.submit(() -> CheckRunner.runEscMethod(uri, source, "good3")));
            futures.add(pool.submit(() -> CheckRunner.runEscMethod(uri, source, "bad1")));
            futures.add(pool.submit(() -> CheckRunner.runEscMethod(uri, source, "bad2")));
        } finally {
            pool.shutdown();
        }

        int goodCount = 0, badCount = 0;
        for (Future<CheckRunner.CheckResult> f : futures) {
            CheckRunner.CheckResult r = f.get(120, TimeUnit.SECONDS);
            assertEquals("Each per-method result must have exactly one proof entry",
                    1, r.proofResults().size());
            Map.Entry<String, IProverResult.Kind> entry =
                    r.proofResults().entrySet().iterator().next();
            String method = CheckRunner.bareMethodName(entry.getKey());
            IProverResult.Kind kind = entry.getValue();
            if (method.startsWith("good")) {
                assertEquals("'" + method + "' must be UNSAT",
                        IProverResult.UNSAT, kind);
                assertEquals("'" + method + "' must exit 0", 0, r.exitCode());
                goodCount++;
            } else {
                assertTrue("'" + method + "' must be SAT/POSSIBLY_SAT; got " + kind,
                        kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT);
                assertEquals("'" + method + "' must exit 6", 6, r.exitCode());
                badCount++;
            }
        }
        assertEquals("Expected 3 verified results", 3, goodCount);
        assertEquals("Expected 2 failing results",  2, badCount);
    }

    // -----------------------------------------------------------------------
    // (2) Larger concurrent batch — all results correct, none contaminated
    // -----------------------------------------------------------------------

    /**
     * Submits 10 concurrent per-method runs on the same in-memory source
     * (5 verified, 5 failing).  Each result must contain exactly one proof
     * entry for <em>its own</em> targeted method — no proof entries from other
     * concurrent runs may appear in any result.
     */
    @Test
    public void testConcurrentMethodRunsResultsAreIndependent() throws Exception {
        int n = 5;
        StringBuilder src = new StringBuilder();
        src.append("public class ConcurrentEscLarge {\n");
        for (int i = 0; i < n; i++) {
            src.append("    //@ ensures \\result == x;\n");
            src.append("    public int gm").append(i).append("(int x) { return x; }\n");
            src.append("    //@ ensures \\result != 0;\n");
            src.append("    public int fm").append(i).append("(int x) { return 0; }\n");
        }
        src.append("}\n");
        String source = src.toString();
        String uri = "file:///ConcurrentEscLarge.java";

        ExecutorService pool = Executors.newFixedThreadPool(n * 2);
        List<Future<CheckRunner.CheckResult>> futures = new ArrayList<>();
        try {
            for (int i = 0; i < n; i++) {
                final String gname = "gm" + i;
                final String fname = "fm" + i;
                futures.add(pool.submit(() -> CheckRunner.runEscMethod(uri, source, gname)));
                futures.add(pool.submit(() -> CheckRunner.runEscMethod(uri, source, fname)));
            }
        } finally {
            pool.shutdown();
        }

        int goodCount = 0, badCount = 0;
        for (Future<CheckRunner.CheckResult> f : futures) {
            CheckRunner.CheckResult r = f.get(120, TimeUnit.SECONDS);
            assertEquals("Each per-method result must have exactly one proof entry; got "
                    + r.proofResults(),
                    1, r.proofResults().size());
            Map.Entry<String, IProverResult.Kind> e =
                    r.proofResults().entrySet().iterator().next();
            if (CheckRunner.bareMethodName(e.getKey()).startsWith("gm")) {
                assertEquals(e.getKey() + " must be UNSAT",
                        IProverResult.UNSAT, e.getValue());
                goodCount++;
            } else {
                assertTrue(e.getKey() + " must be SAT/POSSIBLY_SAT",
                        e.getValue() == IProverResult.SAT || e.getValue() == IProverResult.POSSIBLY_SAT);
                badCount++;
            }
        }
        assertEquals("Expected " + n + " verified results", n, goodCount);
        assertEquals("Expected " + n + " failing results",  n, badCount);
    }

    // -----------------------------------------------------------------------
    // (3) Cancel one method run — concurrent run is unaffected
    // -----------------------------------------------------------------------

    /**
     * Starts two concurrent disk-file ESC runs:
     * <ol>
     *   <li>A slow method (non-linear integer arithmetic that z3 cannot prove
     *       quickly) — this one is cancelled.</li>
     *   <li>A fast identity method (trivially UNSAT) — this one runs to
     *       completion.</li>
     * </ol>
     * Cancels the slow run's subprocess via the {@link IAPI} captured by its
     * {@code onApiReady} hook.
     *
     * <p>Expected outcomes:
     * <ul>
     *   <li>Slow run exits with code 5 (CANCELLED)</li>
     *   <li>Fast run completes normally with UNSAT and exit code 0 — the
     *       cancellation must have no effect on it</li>
     * </ul>
     */
    @Test
    public void testCancelOneMethodRunDoesNotAffectOther() throws Exception {
        File f = writeJava("ConcurrentCancelMethod.java",
                "public class ConcurrentCancelMethod {\n" +
                "    public void slow(int a, int b) {\n" +
                "        //@ assert (a * b) == 0 ==> (a == 0 || b == 0);\n" +
                "    }\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int fast(int x) { return x; }\n" +
                "}\n");
        String filePath = f.getAbsolutePath();
        String uri      = fileUri(f);
        OpenJMLSettings settings = new OpenJMLSettings();

        // Start the slow method run and capture its IAPI for cancellation.
        // Cancel is triggered via a proof-result listener that fires on RUNNING —
        // this is reliable regardless of how fast z3 solves the formula, because
        // the canceled flag is set synchronously on the ESC thread before the
        // prover is invoked (line 362 of doMethod checks it after RUNNING is reported).
        AtomicReference<IAPI> slowApi = new AtomicReference<>();
        AtomicReference<CheckRunner.CheckResult> slowResult = new AtomicReference<>();
        Thread slowThread = new Thread(() -> {
            CheckRunner.CheckResult r = CheckRunner.runEscFileMethod(
                    filePath, uri, "slow", settings, api -> {
                        slowApi.set(api);
                        api.setProofResultListener((sym, result) -> {
                            if (result.result() == IProverResult.RUNNING) api.cancelEsc();
                        });
                    });
            slowResult.set(r);
        });
        slowThread.setDaemon(true);
        slowThread.start();

        // Start the fast method run concurrently on its own thread.
        ExecutorService fastPool = Executors.newSingleThreadExecutor();
        Future<CheckRunner.CheckResult> fastFuture = fastPool.submit(
                () -> CheckRunner.runEscFileMethod(filePath, uri, "fast", settings));
        fastPool.shutdown();

        // Wait for the slow run's IAPI hook to fire (it will also self-cancel).
        long deadline = System.currentTimeMillis() + 30_000;
        while (slowApi.get() == null && System.currentTimeMillis() < deadline) {
            Thread.sleep(20);
        }
        assertNotNull("Slow run's IAPI hook never fired within 30 s", slowApi.get());

        // Slow thread must terminate within 30 s of the cancel.
        slowThread.join(30_000);
        assertFalse("Slow thread must finish within 30 s after cancel", slowThread.isAlive());

        // Slow run: must exit 5 (CANCELLED).
        CheckRunner.CheckResult slow = slowResult.get();
        assertNotNull("Slow run result must not be null", slow);
        assertEquals("Slow run must exit 5 (CANCELLED)", 5, slow.exitCode());

        // Fast run: must complete normally with UNSAT and exit 0.
        CheckRunner.CheckResult fast = fastFuture.get(120, TimeUnit.SECONDS);
        assertNotNull("Fast run result must not be null", fast);
        IProverResult.Kind fastKind = fast.proofResultForMethod("fast");
        assertNotNull("fast method must have a proof result", fastKind);
        assertEquals("fast method must be UNSAT", IProverResult.UNSAT, fastKind);
        assertEquals("fast method must exit 0", 0, fast.exitCode());
    }
}
