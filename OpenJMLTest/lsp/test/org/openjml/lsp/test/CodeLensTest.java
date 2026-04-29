package org.openjml.lsp.test;

import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.JavaSourceScanner;

import java.util.List;

import static org.junit.Assert.*;

/**
 * Tests for the code-lens building block: {@link JavaSourceScanner#findMethodsFromAst}.
 */
public class CodeLensTest extends LspTestBase {

    private static final String URI = "file:///CodeLensTest.java";

    // -----------------------------------------------------------------------
    // AST-based method discovery: findMethodsFromAst after a check pass
    // -----------------------------------------------------------------------

    @Test
    public void testCodeLensFromAst() {
        String source =
                "public class CodeLensTest {\n" +
                "    //@ requires x >= 0;\n" +
                "    //@ ensures \\result >= 0;\n" +
                "    public int abs(int x) { return x < 0 ? -x : x; }\n" +
                "    public int neg(int x) { return -x; }\n" +
                "}\n";
        checkContent(URI, source);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(URI);
        assertNotNull("AST cache entry must exist after check", entry);

        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(entry.ast());

        JavaSourceScanner.MethodInfo abs = methods.stream()
                .filter(m -> m.name().equals("abs")).findFirst().orElse(null);
        JavaSourceScanner.MethodInfo neg = methods.stream()
                .filter(m -> m.name().equals("neg")).findFirst().orElse(null);

        assertNotNull("Method 'abs' must be found by AST walker", abs);
        assertNotNull("Method 'neg' must be found by AST walker", neg);
        assertEquals("abs must be on line 3", 3, abs.startLine());
        assertEquals("neg must be on line 4", 4, neg.startLine());
    }
}
