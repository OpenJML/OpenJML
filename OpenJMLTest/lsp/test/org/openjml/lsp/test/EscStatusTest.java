package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.junit.Test;
import org.openjml.IProverResult;
import org.openjml.lsp.CheckRunner;

import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Tests for per-method ESC proof results ({@link CheckRunner.CheckResult#proofResults()}).
 *
 * Each test verifies the proof-result {@link IProverResult.Kind} reported by
 * OpenJML's {@code IProofResultListener} for the methods in a small Java/JML
 * source snippet, as well as the overall exit code and diagnostic severities.
 *
 * Exit-code convention:
 * <ul>
 *   <li>0 — all methods verified (UNSAT)</li>
 *   <li>1 — syntax/type errors; ESC not attempted</li>
 *   <li>6 — at least one verification failure (SAT/POSSIBLY_SAT/SKIPPED/TIMEOUT/CANCELLED)</li>
 * </ul>
 */
public class EscStatusTest extends LspTestBase {

    // -----------------------------------------------------------------------
    // (1) Check errors: type error prevents ESC from running
    // -----------------------------------------------------------------------

    /**
     * When the source has a type error, OpenJML exits with code 1 (check errors)
     * and ESC is not attempted — the proof-results map is empty.
     */
    @Test
    public void testEscWithCheckErrors() throws Exception {
        String source =
                "public class CheckErr {\n" +
                "    //@ ensures \\result > x;\n" +
                "    public int m(int x) { return \"not an int\"; }\n" +
                "}\n";
        CheckRunner.CheckResult result = runEscResult("file:///CheckErr.java", source);

        assertEquals("Expected exit code 1 for check errors", 1, result.exitCode());
        assertTrue("Expected no proof results when check errors prevent ESC",
                result.proofResults().isEmpty());
        assertFalse("Expected at least one error diagnostic", result.diagnostics().isEmpty());
        assertTrue("Expected all diagnostics to be Error severity",
                result.diagnostics().stream()
                        .allMatch(d -> d.getSeverity() == DiagnosticSeverity.Error));
    }

    // -----------------------------------------------------------------------
    // (2) ESC verification failure
    // -----------------------------------------------------------------------

    /**
     * A method whose postcondition is provably false must produce a
     * SAT/POSSIBLY_SAT proof result (i.e. Not verified) and exit code 6.
     */
    @Test
    public void testEscWithVerificationFailure() throws Exception {
        String source =
                "public class EscFail2 {\n" +
                "    //@ ensures \\result > x;\n" +
                "    public int noOp(int x) { return x; }\n" +
                "}\n";
        CheckRunner.CheckResult result = runEscResult("file:///EscFail2.java", source);

        assertEquals("Expected exit code 6 for ESC verification failure", 6, result.exitCode());

        IProverResult.Kind kind = result.proofResults().get("noOp");
        assertNotNull("Expected a proof result for method noOp", kind);
        assertTrue("Expected SAT or POSSIBLY_SAT for failing method",
                kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT);

        assertFalse("Expected at least one ESC diagnostic", result.diagnostics().isEmpty());
        // ESC failures are reported as MANDATORY_WARNING → LSP Warning, not Error.
        assertTrue("Expected all diagnostics to be Warning severity (ESC failures are warnings)",
                result.diagnostics().stream()
                        .allMatch(d -> d.getSeverity() == DiagnosticSeverity.Warning));
    }

    // -----------------------------------------------------------------------
    // (3) ESC clean: method fully verified
    // -----------------------------------------------------------------------

    /**
     * A method whose postcondition is provably satisfied must produce an
     * UNSAT proof result (i.e. Verified) and exit code 0.
     */
    @Test
    public void testEscVerified() throws Exception {
        String source =
                "public class EscVerified {\n" +
                "    //@ requires x >= 0;\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int identity(int x) { return x; }\n" +
                "}\n";
        CheckRunner.CheckResult result = runEscResult("file:///EscVerified.java", source);

        assertEquals("Expected exit code 0 for clean ESC", 0, result.exitCode());

        IProverResult.Kind kind = result.proofResults().get("identity");
        assertNotNull("Expected a proof result for method identity", kind);
        assertEquals("Expected UNSAT for verified method", IProverResult.UNSAT, kind);

        assertEquals("Expected no ESC diagnostics for verified method",
                0, result.diagnostics().size());
    }

    // -----------------------------------------------------------------------
    // (4) Mixed: one verified, one failing — only Warning diagnostics, no Errors
    // -----------------------------------------------------------------------

    /**
     * When a file has one verified method and one failing method, ESC produces
     * exit code 6 and Warning-severity diagnostics only (no Errors).
     * The verified method still records UNSAT; the failing method records
     * SAT or POSSIBLY_SAT.
     *
     * <pre>
     * line 0: public class MixedEsc {
     * line 1:     //@ ensures \result == x;     — spec for verified
     * line 2:     public int verified(int x) { return x; }
     * line 3:
     * line 4:     //@ ensures \result > x;      — spec for failing
     * line 5:     public int failing(int x) { return x; }
     * line 6: }
     * </pre>
     */
    @Test
    public void testEscWithOnlyWarnings() throws Exception {
        String source =
                "public class MixedEsc {\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int verified(int x) { return x; }\n" +
                "\n" +
                "    //@ ensures \\result > x;\n" +
                "    public int failing(int x) { return x; }\n" +
                "}\n";
        CheckRunner.CheckResult result = runEscResult("file:///MixedEsc.java", source);

        assertEquals("Expected exit code 6 (failure in at least one method)", 6, result.exitCode());

        // Diagnostics from ESC failures are Warning severity, not Error.
        assertFalse("Expected at least one diagnostic", result.diagnostics().isEmpty());
        assertTrue("Expected only Warning-severity diagnostics (ESC failures are warnings, not errors)",
                result.diagnostics().stream()
                        .allMatch(d -> d.getSeverity() == DiagnosticSeverity.Warning));

        // Per-method proof results.
        IProverResult.Kind verifiedKind = result.proofResults().get("verified");
        assertNotNull("Expected a proof result for method 'verified'", verifiedKind);
        assertEquals("Expected UNSAT for 'verified' method", IProverResult.UNSAT, verifiedKind);

        IProverResult.Kind failingKind = result.proofResults().get("failing");
        assertNotNull("Expected a proof result for method 'failing'", failingKind);
        assertTrue("Expected SAT or POSSIBLY_SAT for 'failing' method",
                failingKind == IProverResult.SAT || failingKind == IProverResult.POSSIBLY_SAT);
    }

    // -----------------------------------------------------------------------
    // (5) skipesc annotation
    // -----------------------------------------------------------------------

    /**
     * A method annotated with {@code //@ skipesc} must be reported as
     * {@link IProverResult#SKIPPED} by the proof-result listener and must
     * not produce any ESC diagnostics.
     *
     * <pre>
     * line 0: public class SkipEscTest {
     * line 1:     //@ ensures \result > x;  — would fail without skipesc
     * line 2:     //@ skipesc
     * line 3:     public int m(int x) { return x; }
     * line 4: }
     * </pre>
     */
    @Test
    public void testEscSkipEscAnnotation() throws Exception {
        // The //@ skipesc modifier must appear after any spec clauses,
        // immediately before the method declaration.
        String source =
                "public class SkipEscTest {\n" +
                "    //@ ensures \\result > x;\n" +  // would fail ESC if attempted
                "    //@ skipesc\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n";
        CheckRunner.CheckResult result = runEscResult("file:///SkipEscTest.java", source);

        IProverResult.Kind kind = result.proofResults().get("m");
        assertNotNull("Expected a proof result for method m (should be SKIPPED)", kind);
        assertEquals("Expected SKIPPED for method annotated with //@ skipesc",
                IProverResult.SKIPPED, kind);

        // A skipped method produces no ESC verification diagnostics.
        assertEquals("Expected no ESC diagnostics for skipped method",
                0, result.diagnostics().size());
    }
}
