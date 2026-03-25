package org.openjml.lsp.test;

import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.JavaSourceScanner;

import java.util.List;

import static org.junit.Assert.*;

/**
 * Tests for the code-lens building blocks: {@link JavaSourceScanner}.
 *
 * <p>Code lenses are built from {@link JavaSourceScanner#findMethods} (pre-AST
 * heuristic) or {@link JavaSourceScanner#findMethodsFromAst} (AST-precise), plus
 * {@link JavaSourceScanner#methodFqn}.  These tests verify that method discovery
 * and FQN generation work correctly — covering the full data path from source to
 * the code-lens label and command arguments.
 */
public class CodeLensTest extends LspTestBase {

    private static final String URI = "file:///CodeLensTest.java";

    // -----------------------------------------------------------------------
    // (1) Single method: found with correct line
    // -----------------------------------------------------------------------

    @Test
    public void testCodeLensOneMethod() {
        String source =
                "public class CodeLensTest {\n" +
                "    public int identity(int x) { return x; }\n" +
                "}\n";
        List<JavaSourceScanner.MethodInfo> methods = JavaSourceScanner.findMethods(source);
        assertEquals("Expected exactly one method", 1, methods.size());
        assertEquals("Method name must be 'identity'", "identity", methods.get(0).name());
        assertEquals("Method must be on line 1", 1, methods.get(0).startLine());
    }

    // -----------------------------------------------------------------------
    // (2) Multiple methods: each found at the correct line
    // -----------------------------------------------------------------------

    @Test
    public void testCodeLensMultipleMethods() {
        String source =
                "public class CodeLensTest {\n" +      // line 0
                "    public int first(int x) { return x; }\n" +  // line 1
                "\n" +                                  // line 2
                "    public int second(int y) { return y; }\n" + // line 3
                "}\n";
        List<JavaSourceScanner.MethodInfo> methods = JavaSourceScanner.findMethods(source);
        assertEquals("Expected two methods", 2, methods.size());
        assertEquals("first must be on line 1", 1, methods.get(0).startLine());
        assertEquals("second must be on line 3", 3, methods.get(1).startLine());
        assertEquals("first method name", "first",  methods.get(0).name());
        assertEquals("second method name", "second", methods.get(1).name());
    }

    // -----------------------------------------------------------------------
    // (3) No methods: class body with no methods returns empty list
    // -----------------------------------------------------------------------

    @Test
    public void testCodeLensNoMethods() {
        String source =
                "public class CodeLensTest {\n" +
                "    public int x;\n" +
                "    private String s;\n" +
                "}\n";
        List<JavaSourceScanner.MethodInfo> methods = JavaSourceScanner.findMethods(source);
        assertTrue("Expected no methods for field-only class", methods.isEmpty());
    }

    // -----------------------------------------------------------------------
    // (4) FQN generation: package + class + method
    // -----------------------------------------------------------------------

    @Test
    public void testCodeLensCommandArgsFqn() {
        String source =
                "package com.example;\n" +
                "public class MyClass {\n" +
                "    public void doWork() {}\n" +
                "}\n";
        String fqn = JavaSourceScanner.methodFqn(source, "doWork");
        assertEquals("FQN must include package, class, and method name",
                "com.example.MyClass.doWork", fqn);
    }

    // -----------------------------------------------------------------------
    // (5) AST-based method discovery: findMethodsFromAst after a check pass
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
                JavaSourceScanner.findMethodsFromAst(entry.ast(), source);

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
