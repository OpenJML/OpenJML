package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.eclipse.lsp4j.Range;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * End-to-end tests for OpenJML LSP diagnostic reporting.
 *
 * Each test submits Java/JML source through the in-process LSP connection
 * established by {@link LspTestBase} and asserts on the diagnostics received
 * via {@code textDocument/publishDiagnostics}.
 */
public class DiagnosticsTest extends LspTestBase {

    /** A syntactically and semantically valid Java class should produce no diagnostics. */
    @Test
    public void testCleanJavaProducesNoDiagnostics() throws Exception {
        String source =
                "public class Clean {\n" +
                "    public int add(int a, int b) { return a + b; }\n" +
                "}\n";
        List<Diagnostic> diags = checkContent("file:///Clean.java", source);
        assertEquals("Expected no diagnostics for clean Java source", 0, diags.size());
    }

    /** A Java syntax error must produce at least one Error-severity diagnostic. */
    @Test
    public void testSyntaxErrorProducesErrorDiagnostic() throws Exception {
        // Missing closing parenthesis on the method signature
        String source =
                "public class Bad {\n" +
                "    public void m(  {\n" +
                "    }\n" +
                "}\n";
        List<Diagnostic> diags = checkContent("file:///Bad.java", source);
        assertFalse("Expected at least one diagnostic for syntax error", diags.isEmpty());
        assertTrue("Expected an ERROR-severity diagnostic",
                diags.stream().anyMatch(d -> d.getSeverity() == DiagnosticSeverity.Error));
    }

    /** A type error must produce at least one Error-severity diagnostic. */
    @Test
    public void testTypeErrorProducesErrorDiagnostic() throws Exception {
        String source =
                "public class TypeErr {\n" +
                "    public int m() { return \"not an int\"; }\n" +
                "}\n";
        List<Diagnostic> diags = checkContent("file:///TypeErr.java", source);
        assertFalse("Expected at least one diagnostic for type error", diags.isEmpty());
        assertTrue("Expected an ERROR-severity diagnostic",
                diags.stream().anyMatch(d -> d.getSeverity() == DiagnosticSeverity.Error));
    }

    /**
     * A JML spec that is syntactically valid should not produce diagnostics
     * during a --check pass (ESC would be needed to detect proof failures).
     */
    @Test
    public void testValidJmlSpecProducesNoDiagnostics() throws Exception {
        String source =
                "public class JmlOk {\n" +
                "    //@ requires x > 0;\n" +
                "    //@ ensures \\result > 0;\n" +
                "    public int m(int x) { return x + 1; }\n" +
                "}\n";
        List<Diagnostic> diags = checkContent("file:///JmlOk.java", source);
        assertNotNull(diags);
        assertEquals("Expected no diagnostics for syntactically valid JML spec", 0, diags.size());
    }

    /** A malformed JML annotation should produce a diagnostic. */
    @Test
    public void testMalformedJmlAnnotationProducesDiagnostic() throws Exception {
        String source =
                "public class JmlBad {\n" +
                "    //@ requires ;\n" +   // empty requires clause
                "    public void m() {}\n" +
                "}\n";
        List<Diagnostic> diags = checkContent("file:///JmlBad.java", source);
        assertFalse("Expected at least one diagnostic for malformed JML", diags.isEmpty());
    }

    /**
     * A method whose postcondition is provably satisfied must produce no ESC diagnostics.
     * Uses only primitive int parameters to avoid spec-loading issues with class types.
     */
    @Test
    public void testEscCleanMethodProducesNoDiagnostics() throws Exception {
        String source =
                "public class EscOk {\n" +
                "    //@ requires x >= 0;\n" +
                "    //@ ensures \\result == x;\n" +
                "    public int identity(int x) { return x; }\n" +
                "}\n";
        List<Diagnostic> diags = runEscContent("file:///EscOk.java", source);
        assertEquals("Expected no ESC diagnostics for a provably correct method", 0, diags.size());
    }

    /**
     * A method whose postcondition is NOT satisfied must produce at least one ESC diagnostic.
     * The method returns x but the postcondition requires the result to be strictly greater
     * than x, which is always false.
     */
    @Test
    public void testEscPostconditionViolationProducesDiagnostic() throws Exception {
        String source =
                "public class EscFail {\n" +
                "    //@ ensures \\result > x;\n" +
                "    public int noOp(int x) { return x; }\n" +
                "}\n";
        List<Diagnostic> diags = runEscContent("file:///EscFail.java", source);
        assertFalse("Expected at least one ESC diagnostic for postcondition violation",
                diags.isEmpty());
    }

    /**
     * Source with two methods, both with provably false postconditions.
     * Used by the per-method ESC tests below.
     *
     * <pre>
     * line 0: public class TwoFailing {
     * line 1:     //@ ensures \result > x;       // methodA spec
     * line 2:     public int methodA(int x) { return x; }
     * line 3:
     * line 4:     //@ ensures \result < x;       // methodB spec
     * line 5:     public int methodB(int x) { return x; }
     * line 6: }
     * </pre>
     *
     * methodA occupies lines 1–3, methodB occupies lines 4–6.
     * Running full ESC produces diagnostics for both; running with
     * {@code --method TwoFailing.methodA} or {@code .methodB} restricts results
     * to one method.
     */
    private static final String TWO_FAILING_SOURCE =
            "public class TwoFailing {\n" +
            "    //@ ensures \\result > x;\n" +
            "    public int methodA(int x) { return x; }\n" +
            "\n" +
            "    //@ ensures \\result < x;\n" +
            "    public int methodB(int x) { return x; }\n" +
            "}\n";

    // methodA occupies lines 1–3 (0-based); methodB occupies lines 4–6.
    private static final int METHOD_B_FIRST_LINE = 4;

    /**
     * When {@code --method} is not used, full ESC on {@code TwoFailing} should
     * report diagnostics for both methods.
     */
    @Test
    public void testEscBothMethodsFailWithoutMethodFilter() throws Exception {
        List<Diagnostic> diags = runEscContent("file:///TwoFailing.java", TWO_FAILING_SOURCE);
        assertFalse("Expected ESC diagnostics for both failing methods", diags.isEmpty());
        boolean hasMethodA = diags.stream()
                .anyMatch(d -> d.getRange().getStart().getLine() < METHOD_B_FIRST_LINE);
        boolean hasMethodB = diags.stream()
                .anyMatch(d -> d.getRange().getStart().getLine() >= METHOD_B_FIRST_LINE);
        assertTrue("Expected at least one diagnostic in methodA's line range", hasMethodA);
        assertTrue("Expected at least one diagnostic in methodB's line range", hasMethodB);
    }

    /**
     * Running ESC with {@code --method TwoFailing.methodA} should return diagnostics
     * only for {@code methodA} (lines 1–3), not for {@code methodB} (lines 4–6).
     */
    @Test
    public void testEscForMethodAReturnsOnlyMethodAErrors() throws Exception {
        List<Diagnostic> diags = runEscContentMethod(
                "file:///TwoFailing.java", TWO_FAILING_SOURCE, "TwoFailing.methodA");
        assertFalse("Expected at least one ESC diagnostic for methodA", diags.isEmpty());
        assertTrue("Expected all diagnostics to be within methodA's line range (< line " + METHOD_B_FIRST_LINE + ")",
                diags.stream().allMatch(d -> d.getRange().getStart().getLine() < METHOD_B_FIRST_LINE));
    }

    /**
     * Running ESC with {@code --method TwoFailing.methodB} should return diagnostics
     * only for {@code methodB} (lines 4–6), not for {@code methodA} (lines 1–3).
     */
    @Test
    public void testEscForMethodBReturnsOnlyMethodBErrors() throws Exception {
        List<Diagnostic> diags = runEscContentMethod(
                "file:///TwoFailing.java", TWO_FAILING_SOURCE, "TwoFailing.methodB");
        assertFalse("Expected at least one ESC diagnostic for methodB", diags.isEmpty());
        assertTrue("Expected all diagnostics to be within methodB's line range (>= line " + METHOD_B_FIRST_LINE + ")",
                diags.stream().allMatch(d -> d.getRange().getStart().getLine() >= METHOD_B_FIRST_LINE));
    }

    /**
     * Diagnostics must carry a non-trivial range covering the offending token,
     * not just a single-character point.
     *
     * <p>Source layout (0-indexed lines/columns):
     * <pre>
     * line 0: public class RangeCheck {
     * line 1:     public int m() { return "oops"; }
     *                                      ^----^  cols 28–33  (span = 6 = len("oops"))
     * line 2: }
     * </pre>
     * The type-mismatch diagnostic must land on line 1 with startCol == 28 and
     * endCol == 34 (startCol + spanLength, exclusive).  Both start and end must
     * be on the same line (the range does not span newlines).
     */
    @Test
    public void testDiagnosticRangeCoversToken() throws Exception {
        // Line 1: "    public int m() { return "oops"; }"
        //          0123456789012345678901234567890123456
        //          0         1         2         3
        // "oops" starts at col 28 (0-indexed), length 6.
        String source =
                "public class RangeCheck {\n" +
                "    public int m() { return \"oops\"; }\n" +
                "}\n";
        List<Diagnostic> diags = checkContent("file:///RangeCheck.java", source);
        assertFalse("Expected at least one diagnostic", diags.isEmpty());

        // Find the type-error diagnostic on line 1.
        Diagnostic d = diags.stream()
                .filter(x -> x.getRange().getStart().getLine() == 1)
                .findFirst()
                .orElse(null);
        assertNotNull("Expected a diagnostic on line 1", d);

        Range range = d.getRange();
        int startLine = range.getStart().getLine();
        int endLine   = range.getEnd().getLine();
        int startCol  = range.getStart().getCharacter();
        int endCol    = range.getEnd().getCharacter();

        assertEquals("Range must not span multiple lines", startLine, endLine);
        assertTrue("Range end column must be greater than start column (non-point range)",
                endCol > startCol);
        assertEquals("startCol: \"oops\" starts at column 28", 28, startCol);
        assertEquals("endCol: \"oops\" ends at column 34 (28 + len(\"oops\"))", 34, endCol);
    }

    /** Diagnostics carry a non-null source field identifying OpenJML. */
    @Test
    public void testDiagnosticSourceIsOpenjml() throws Exception {
        String source =
                "public class SrcCheck {\n" +
                "    public int m() { return \"oops\"; }\n" +
                "}\n";
        List<Diagnostic> diags = checkContent("file:///SrcCheck.java", source);
        assertFalse(diags.isEmpty());
        assertTrue("Expected source='openjml' on all diagnostics",
                diags.stream().allMatch(d -> "openjml".equals(d.getSource())));
    }
}
