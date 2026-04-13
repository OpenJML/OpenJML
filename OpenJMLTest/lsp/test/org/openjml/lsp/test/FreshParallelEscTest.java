package org.openjml.lsp.test;

import org.junit.Test;
import org.openjml.IProverResult;
import org.openjml.lsp.CheckRunner;

import static org.junit.Assert.*;

/**
 * Tests for the {@code "fresh"} ESC engine: each method gets its own fresh
 * {@link org.openjml.IAPI} instance and all run concurrently in the thread pool.
 *
 * <p>The tests mirror {@link DoEscTest} but call
 * {@link CheckRunner#runFreshParallelEscFile} instead of
 * {@link CheckRunner#runDoEscFile}.  Results must be identical: correct
 * proof outcomes, correct diagnostics, correct exit codes.
 */
public class FreshParallelEscTest extends LspTestBase {

    // -----------------------------------------------------------------------
    // (1) Single method — verified
    // -----------------------------------------------------------------------

    @Test
    public void testFreshSingleMethodVerified() throws Exception {
        String uri = "file:///FreshVerified.java";
        String source =
                "public class FreshVerified {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int id(int x) { return x; }\n" +
                "}\n";

        CheckRunner.CheckResult result = runFreshParallelEscFileResult(uri, source);
        assertEquals("exit 0 for verified method", 0, result.exitCode());

        IProverResult.Kind kind = result.proofResultForMethod("id");
        assertNotNull("Expected proof result for 'id'", kind);
        assertEquals("Expected UNSAT for verified method; got " + kind,
                IProverResult.UNSAT, kind);
        assertTrue("Expected no diagnostics for verified method",
                result.diagnostics().isEmpty());
    }

    // -----------------------------------------------------------------------
    // (2) Single method — failing postcondition
    // -----------------------------------------------------------------------

    @Test
    public void testFreshSingleMethodFails() throws Exception {
        String uri = "file:///FreshFail.java";
        String source =
                "public class FreshFail {\n" +
                "    //@ ensures \\result != 0;\n" +
                "    public int zero(int x) { return 0; }\n" +
                "}\n";

        CheckRunner.CheckResult result = runFreshParallelEscFileResult(uri, source);
        assertEquals("exit 6 for failing method", 6, result.exitCode());

        IProverResult.Kind kind = result.proofResultForMethod("zero");
        assertNotNull("Expected proof result for 'zero'", kind);
        assertTrue("Expected SAT/POSSIBLY_SAT; got " + kind,
                kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT);
        assertFalse("Expected at least one diagnostic", result.diagnostics().isEmpty());
    }

    // -----------------------------------------------------------------------
    // (3) Mixed verified and failing methods — concurrent execution
    // -----------------------------------------------------------------------

    @Test
    public void testFreshMixedMethods() throws Exception {
        String uri = "file:///FreshMixed.java";
        String source =
                "public class FreshMixed {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int good(int x) { return x; }\n" +
                "    //@ ensures \\result != 0;\n" +
                "    public int bad(int x) { return 0; }\n" +
                "}\n";

        CheckRunner.CheckResult result = runFreshParallelEscFileResult(uri, source);
        assertEquals("exit 6 when any method fails", 6, result.exitCode());

        IProverResult.Kind goodKind = result.proofResultForMethod("good");
        IProverResult.Kind badKind  = result.proofResultForMethod("bad");
        assertNotNull("Expected proof result for 'good'", goodKind);
        assertNotNull("Expected proof result for 'bad'",  badKind);
        assertEquals("'good' should be UNSAT; got " + goodKind,
                IProverResult.UNSAT, goodKind);
        assertTrue("'bad' should be SAT/POSSIBLY_SAT; got " + badKind,
                badKind == IProverResult.SAT || badKind == IProverResult.POSSIBLY_SAT);
    }

    // -----------------------------------------------------------------------
    // (4) Many methods — all run concurrently, all results correct
    // -----------------------------------------------------------------------

    @Test
    public void testFreshConcurrentManyMethods() throws Exception {
        String uri = "file:///FreshMany.java";

        // 6 verified (mV0..mV5) and 6 failing (mF0..mF5) methods.
        int pairs = 6;
        StringBuilder src = new StringBuilder();
        src.append("public class FreshMany {\n");
        for (int i = 0; i < pairs; i++) {
            src.append("    //@ ensures \\result == x;\n");
            src.append("    public int mV").append(i).append("(int x) { return x; }\n");
            src.append("    //@ ensures \\result != 0;\n");
            src.append("    public int mF").append(i).append("(int x) { return 0; }\n");
        }
        src.append("}\n");

        CheckRunner.CheckResult result = runFreshParallelEscFileResult(uri, src.toString());
        assertEquals("exit 6 when any method fails", 6, result.exitCode());

        int verifiedCount = 0;
        int failedCount   = 0;
        for (var entry : result.proofResults().entrySet()) {
            String name = CheckRunner.bareMethodName(entry.getKey());
            IProverResult.Kind kind = entry.getValue();
            if (name.startsWith("mV")) {
                verifiedCount++;
                assertEquals("mV method should be UNSAT; got " + kind + " for " + name,
                        IProverResult.UNSAT, kind);
            } else if (name.startsWith("mF")) {
                failedCount++;
                assertTrue("mF method should be SAT/POSSIBLY_SAT; got " + kind + " for " + name,
                        kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT);
            }
        }
        assertEquals("Expected " + pairs + " verified results", pairs, verifiedCount);
        assertEquals("Expected " + pairs + " failing results",  pairs, failedCount);
    }
}
