package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.junit.Test;
import org.openjml.IProverResult;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.DiagnosticConverter;
import org.openjml.lsp.OpenJMLSettings;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import static org.junit.Assert.*;

/**
 * Tests for the in-process {@code doESC} path ({@code escEngine=api}).
 *
 * <p>The doESC path reuses the IAPI instance stored by a successful {@code --check} run
 * instead of spawning a fresh OpenJML subprocess for each ESC request.  These tests verify:
 * <ul>
 *   <li>Single-method doESC on a verified method (UNSAT)</li>
 *   <li>Single-method doESC on a method with a failing postcondition (SAT/POSSIBLY_SAT)</li>
 *   <li>Full-file doESC on a class with many methods — some verified, some failing</li>
 *   <li>Concurrent doESC submission on 12 methods (calls are serialized internally via
 *       the entry's {@code escLock}, but the calling code submits them concurrently to
 *       a thread pool and all results are collected correctly)</li>
 *   <li>Fallback to subprocess when no cached IAPI is available</li>
 * </ul>
 *
 * <p>Verified methods use {@code id(int x) { return x; }} with postcondition
 * {@code \result == x} — no arithmetic, no overflow risk, trivially UNSAT.
 * Failing methods use {@code zero(int x) { return 0; }} with postcondition
 * {@code \result != 0} — always has a counterexample.
 */
public class DoEscTest extends LspTestBase {

    // -----------------------------------------------------------------------
    // (1) Single-method doESC — verified
    // -----------------------------------------------------------------------

    @Test
    public void testDoEscSingleMethodVerified() throws Exception {
        String uri = "file:///DoEscVerified.java";
        String source =
                "public class DoEscVerified {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int id(int x) { return x; }\n" +
                "}\n";

        CheckRunner.CheckResult result = runDoEscMethodResult(uri, source, "id");
        assertEquals("doESC should exit 0 for verified method", 0, result.exitCode());

        IProverResult.Kind kind = result.proofResultForMethod("id");
        assertNotNull("Expected a proof result for 'id'", kind);
        assertEquals("Expected UNSAT for verified method; got " + kind,
                IProverResult.UNSAT, kind);
        assertTrue("Expected no ESC diagnostics for verified method",
                result.diagnostics().isEmpty());
    }

    // -----------------------------------------------------------------------
    // (2) Single-method doESC — failing postcondition
    // -----------------------------------------------------------------------

    @Test
    public void testDoEscSingleMethodFails() throws Exception {
        String uri = "file:///DoEscFail.java";
        String source =
                "public class DoEscFail {\n" +
                "    //@ ensures \\result != 0;\n" +
                "    public int zero(int x) { return 0; }\n" +
                "}\n";

        CheckRunner.CheckResult result = runDoEscMethodResult(uri, source, "zero");
        assertEquals("doESC should exit 6 for failing method", 6, result.exitCode());

        IProverResult.Kind kind = result.proofResultForMethod("zero");
        assertNotNull("Expected a proof result for 'zero'", kind);
        assertTrue("Expected SAT/POSSIBLY_SAT for failing method; got " + kind,
                kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT);
        assertFalse("Expected at least one ESC diagnostic for failing method",
                result.diagnostics().isEmpty());
    }

    // -----------------------------------------------------------------------
    // (3) Full-file doESC — mix of verified and failing methods
    // -----------------------------------------------------------------------

    @Test
    public void testDoEscFileResult() throws Exception {
        String uri = "file:///DoEscMixed.java";
        String source =
                "public class DoEscMixed {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int good(int x) { return x; }\n" +
                "    //@ ensures \\result != 0;\n" +
                "    public int bad(int x) { return 0; }\n" +
                "}\n";

        CheckRunner.CheckResult result = runDoEscFileResult(uri, source);
        assertEquals("doESC on whole file should exit 6 when any method fails",
                6, result.exitCode());

        IProverResult.Kind goodKind = result.proofResultForMethod("good");
        IProverResult.Kind badKind  = result.proofResultForMethod("bad");
        assertNotNull("Expected a proof result for 'good'", goodKind);
        assertNotNull("Expected a proof result for 'bad'",  badKind);
        assertEquals("'good' should be UNSAT; got " + goodKind,
                IProverResult.UNSAT, goodKind);
        assertTrue("'bad' should be SAT/POSSIBLY_SAT; got " + badKind,
                badKind == IProverResult.SAT || badKind == IProverResult.POSSIBLY_SAT);
    }

    // -----------------------------------------------------------------------
    // (4) Concurrent doESC on 12 methods — correct results for all
    // -----------------------------------------------------------------------

    /**
     * Build a class with {@code n} pairs of (verified, failing) methods and
     * submit doESC for each method concurrently.  Despite the internal lock
     * serializing the actual doESC calls, all results must be collected
     * correctly.
     *
     * <p>Verified methods: {@code mVi(int x) { return x; }} with
     * {@code ensures \result == x;} — UNSAT, no diagnostics, exit 0.
     * Failing methods: {@code mFi(int x) { return 0; }} with
     * {@code ensures \result != 0;} — SAT/POSSIBLY_SAT, diagnostics, exit 6.
     */
    @Test
    public void testDoEscConcurrentManyMethods() throws Exception {
        String uri = "file:///DoEscMany.java";

        // 6 verified methods (mV0..mV5) and 6 failing methods (mF0..mF5).
        StringBuilder src = new StringBuilder();
        src.append("public class DoEscMany {\n");
        int pairs = 6;
        for (int i = 0; i < pairs; i++) {
            src.append("    //@ ensures \\result == x;\n");
            src.append("    public int mV").append(i).append("(int x) { return x; }\n");
            src.append("    //@ ensures \\result != 0;\n");
            src.append("    public int mF").append(i).append("(int x) { return 0; }\n");
        }
        src.append("}\n");
        String source = src.toString();

        // --check first so IAPI is stored in cache.
        CheckRunner.CheckResult check = CheckRunner.check(uri, source);
        assertEquals("--check must succeed for doESC to work", 0, check.exitCode());

        OpenJMLSettings settings = new OpenJMLSettings();
        ExecutorService pool = Executors.newFixedThreadPool(12);
        List<Future<CheckRunner.CheckResult>> futures = new ArrayList<>();

        // Submit all 12 doESC tasks concurrently.
        for (int i = 0; i < pairs; i++) {
            final String verifiedName = "mV" + i;
            final String failingName  = "mF" + i;
            futures.add(pool.submit(() -> CheckRunner.runDoEscMethod(uri, verifiedName, settings)));
            futures.add(pool.submit(() -> CheckRunner.runDoEscMethod(uri, failingName,  settings)));
        }
        pool.shutdown();

        // Collect and verify all results.
        int verifiedCount = 0;
        int failedCount   = 0;
        for (Future<CheckRunner.CheckResult> f : futures) {
            CheckRunner.CheckResult r = f.get();   // waits; propagates exceptions
            // Each result covers exactly one method.
            assertEquals("Each per-method result should have exactly one proof entry",
                    1, r.proofResults().size());
            Map.Entry<String, IProverResult.Kind> entry =
                    r.proofResults().entrySet().iterator().next();
            String name = CheckRunner.bareMethodName(entry.getKey());
            IProverResult.Kind kind = entry.getValue();

            if (name.startsWith("mV")) {
                verifiedCount++;
                assertEquals("mV method should be UNSAT; got " + kind + " for " + name,
                        IProverResult.UNSAT, kind);
                assertTrue("mV method should produce no diagnostics; got "
                        + r.diagnostics().size() + " for " + name,
                        r.diagnostics().isEmpty());
            } else {
                failedCount++;
                assertTrue("mF method should be SAT/POSSIBLY_SAT; got " + kind + " for " + name,
                        kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT);
                assertEquals("mF method should exit 6; got " + r.exitCode() + " for " + name,
                        6, r.exitCode());
                assertFalse("mF method should produce diagnostics; got none for " + name,
                        r.diagnostics().isEmpty());
            }
        }

        assertEquals("Expected " + pairs + " verified results", pairs, verifiedCount);
        assertEquals("Expected " + pairs + " failing results",  pairs, failedCount);
    }

    // -----------------------------------------------------------------------
    // (5) Fallback to subprocess when no cached IAPI exists
    // -----------------------------------------------------------------------

    @Test
    public void testDoEscFallbackWhenNoCache() throws Exception {
        // Use a fresh URI that has never been --checked in this JVM session.
        String uri = "file:///DoEscFallback_" + System.nanoTime() + ".java";

        // Call runDoEscMethod WITHOUT a prior --check.  The IAPI cache is empty,
        // so it should fall back to the subprocess path and still succeed.
        CheckRunner.CheckResult result =
                CheckRunner.runDoEscMethod(uri, "id", new OpenJMLSettings());
        // The fallback runs runEscFileMethod which requires a real file on disk.
        // Since the file doesn't exist on disk either, we just verify no exception
        // is thrown and a result is returned (exit code may be non-zero).
        assertNotNull("runDoEscMethod should return a result even when fallback fails", result);
    }

    // -----------------------------------------------------------------------
    // (6) doESC diagnostics must carry source tag "openjml.esc", not "openjml.check"
    // -----------------------------------------------------------------------

    /**
     * Diagnostics produced by in-process doESC (api mode) must have
     * {@code source == "openjml.esc"}.  Before the fix, {@code doEscOneMethod}
     * called {@code toLspDiagnosticsFromList} without an explicit source tag,
     * which defaulted to {@code SOURCE_CHECK ("openjml.check")}.
     */
    @Test
    public void testDoEscDiagnosticsHaveEscSourceTag() throws Exception {
        String uri = "file:///DoEscSourceTag.java";
        String source =
                "public class DoEscSourceTag {\n" +
                "    //@ ensures \\result != 0;\n" +
                "    public int zero(int x) { return 0; }\n" +
                "}\n";

        CheckRunner.CheckResult result = runDoEscMethodResult(uri, source, "zero");
        assertFalse("Expected at least one ESC diagnostic for 'ensures \\result != 0'",
                result.diagnostics().isEmpty());

        for (Diagnostic d : result.diagnostics()) {
            assertEquals(
                    "doESC diagnostics must carry source '" + DiagnosticConverter.SOURCE_ESC
                            + "', not '" + d.getSource() + "'",
                    DiagnosticConverter.SOURCE_ESC, d.getSource());
        }
    }
}
