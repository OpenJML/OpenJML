package org.openjml.lsp.test;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
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
