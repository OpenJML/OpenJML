package org.jmlspecs.openjmltest.testsuites;

import java.util.List;

import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.ext.RecommendsClause;
import org.jmlspecs.openjmltest.ParseBase;
import org.junit.*;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;

/** Tests that the parser creates the correct tokens for some simple
 * compilation unit tests, in particular for refines and import statements.
 * @author David Cok
 *
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class compilationUnit extends ParseBase {

    @Override @Before
    public void setUp() throws Exception {
//        jmldebug = true;
        super.setUp();
        postOptions();
    }
    
    /** Compiles the given string as the content of a compilation unit,
     * comparing the parse tree found to the expected node types and character
     * positions found in the second argument.
     * as a compilation unit, each node is represented by a node type (instance 
     * of Class) and character position (an int).
     * 
     * In this case the parse should be successful,
     */
    public void checkCompilationUnit(String text, Object ... expected) {
        List<JCTree> out = parseCompilationUnit(text);
        checkParseTree(out,expected);
        checkDiagnostics(); // Checks that there are no diagnostics
    }

    /** Test harness test */
    public void checkParseFailure(String failureMessage, String text, Object ... expected) {
        boolean failed = false;
        try {
            if (skip) return;
            checkCompilationUnit(text,expected);
        } catch (AssertionError a) {
            failed = true;
            Assert.assertEquals("Failure message was incorrect in checkCompilationUnitFailure", failureMessage, a.getMessage());
        }
        Assert.assertTrue("Test Harness failed to report an error", failed);
    }
    
    ////////////////////////////////////////////////////////////////
    /** Quickie test of some pure Java code */
    @Test
    public void testSomeJava() {
        checkCompilationUnit("package t; \nclass A{}",
                JmlCompilationUnit.class,0,
                JCPackageDecl.class, 0,
                JCIdent.class, 8,
                JmlClassDecl.class, 12,
                JmlModifiers.class, -1);
    }
    
    /** Tests a star import */
    @Test
    public void testImports() {
        checkCompilationUnit("import java.io.*;  class A{}",
                JmlCompilationUnit.class, 0,0,28,
                JmlImport.class, 0,0,17,
                JCFieldAccess.class, 7,14,16,
                JCFieldAccess.class, 7,11,14,
                JCIdent.class, 7,7,11,
                JmlClassDecl.class, 19,19,28,
                JmlModifiers.class, -1,-1,-1);
    }
    
    /** Tests a static star import */
    @Test
    public void testImports2() {
        checkCompilationUnit("import static java.io.*;  class A{}",
                JmlCompilationUnit.class, 0,0,35,
                JmlImport.class, 0,0,24,
                JCFieldAccess.class, 14,21,23,
                JCFieldAccess.class, 14,18,21,
                JCIdent.class, 14,14,18,
                JmlClassDecl.class, 26,26,35,
                JmlModifiers.class, -1,-1,-1);
    }
    
    /** Tests a static non-star import */
    @Test
    public void testImports3() {
        checkCompilationUnit("import static java.io.File;  class A{}",
                JmlCompilationUnit.class, 0,0,38,
                JmlImport.class, 0,0,27,
                JCFieldAccess.class, 14,21,26,
                JCFieldAccess.class, 14,18,21,
                JCIdent.class, 14,14,18,
                JmlClassDecl.class, 29,29,38,
                JmlModifiers.class, -1,-1,-1);
    }
    
    /** Tests a non-star import with modifier */
    @Test
    public void testImports4() {
        checkCompilationUnit("import java.io.File;  public class A{}",
                JmlCompilationUnit.class, 0,0,38,
                JmlImport.class, 0,0,20,
                JCFieldAccess.class, 7,14,19,
                JCFieldAccess.class, 7,11,14,
                JCIdent.class, 7,7,11,
                JmlClassDecl.class, 22,29,38,
                JmlModifiers.class, 22,22,28);
    }
    
    /** Tests a non-star import with 2 modifiers */
    @Test
    public void testImports5() {
        checkCompilationUnit("import java.io.File;  public protected class A{}",
                JmlCompilationUnit.class, 0,0,48,
                JmlImport.class, 0,0,20,
                JCFieldAccess.class, 7,14,19,
                JCFieldAccess.class, 7,11,14,
                JCIdent.class, 7,7,11,
                JmlClassDecl.class, 22,39,48,
                JmlModifiers.class, 22,22,38);
    }
    
    /** Tests a non-star import with 2 modifiers */
    @Test // Just checking correct testing with not all positions present
    public void testImports5a() {
        checkCompilationUnit("import java.io.File;  public protected class A{}",
                JmlCompilationUnit.class, 0,48,
                JmlImport.class, 0,20,
                JCFieldAccess.class, 7,19,
                JCFieldAccess.class, 7,14,
                JCIdent.class, 7,7,11,
                JmlClassDecl.class, 39,
                JmlModifiers.class, 22,22,38);
    }
    
    /** Tests parsing an annotation */
    @Test
    public void testAnnotation() {
        checkCompilationUnit("@org.jmlspecs.annotation.Pure class A {}",
                JmlCompilationUnit.class, 0,0,40,
                JmlClassDecl.class, 0,30,40,
                JmlModifiers.class, 0,0,29,
                JmlAnnotation.class, 0,0,29,
                JCFieldAccess.class, 1,24,29,
                JCFieldAccess.class, 1,13,24,
                JCFieldAccess.class, 1,4,13,
                JCIdent.class, 1,1,4
                );
    }

    /** Tests parsing an annotation and modifier */
    @Test
    public void testAnnotation1() {
        checkCompilationUnit("@org.jmlspecs.annotation.Pure public class A {}",
                JmlCompilationUnit.class, 0,0,47,
                JmlClassDecl.class, 0,37,47,
                JmlModifiers.class, 0,0,36,
                JmlAnnotation.class, 0,0,29,
                JCFieldAccess.class, 1,24,29,
                JCFieldAccess.class, 1,13,24,
                JCFieldAccess.class, 1,4,13,
                JCIdent.class, 1,1,4
                );
    }

    /** Tests parsing an annotation and modifier and annotation */
    @Test
    public void testAnnotation1a() {
        checkCompilationUnit("@org.jmlspecs.annotation.Pure public @org.jmlspecs.annotation.NonNull class A {}",
                JmlCompilationUnit.class, 0,0,80,
                JmlClassDecl.class, 0,70,80,
                JmlModifiers.class, 0,0,69,
                JmlAnnotation.class, 0,0,29,
                JCFieldAccess.class, 1,24,29,
                JCFieldAccess.class, 1,13,24,
                JCFieldAccess.class, 1,4,13,
                JCIdent.class, 1,1,4,
                JmlAnnotation.class, 37,37,69,
                JCFieldAccess.class, 38,61,69,
                JCFieldAccess.class, 38,50,61,
                JCFieldAccess.class, 38,41,50,
                JCIdent.class, 38,38,41
                );
    }

    /** Tests parsing a modifier */
    @Test
    public void testAnnotation2() {
        checkCompilationUnit("/*@ pure */ class A {}"
        ,JmlCompilationUnit.class, 0,0,22
        ,JmlClassDecl.class, 4,12,22
        ,JmlModifiers.class, 4,4,11 // FIXME - would like this to be 8
        );
    }
    
    @Test
    public void testRefining() {
        checkCompilationUnit("class A { void m() { /*@ refining requires true; ensures true; */ m(); }}",
              JmlCompilationUnit.class, 0,0,73,
              JmlClassDecl.class, 0,0,73,
              JmlModifiers.class, -1,-1,-1,
              JmlMethodDecl.class, 10,15,72,
              JmlModifiers.class, -1,-1,-1,
              JCPrimitiveTypeTree.class, 10,10,14,
              JmlBlock.class, 19,19,72,
              JmlStatementSpec.class, 25, 25, 62, 
              JmlMethodSpecs.class, 34, 34, 62,
              JmlSpecificationCase.class, 34,34,62,
              JmlModifiers.class, -1,-1,-1,
              JmlMethodClauseExpr.class, 34,34,48,
              JCLiteral.class, 43,43,47,
              JmlMethodClauseExpr.class, 49,49,62,
              JCLiteral.class, 57,57,61,
              JCExpressionStatement.class, 66,66,70,
              JCMethodInvocation.class, 66,67,69,
              JCIdent.class, 66,66,67
        );
    }
    
    @Test
    public void testRefining2() {
        checkCompilationUnit("class A { void m() { /*@ refining recommends true else NullPointerException; ensures true; */ m(); }}",
              JmlCompilationUnit.class, 0,0,101,
              JmlClassDecl.class, 0,0,101,
              JmlModifiers.class, -1,-1,-1,
              JmlMethodDecl.class, 10,15,100,
              JmlModifiers.class, -1,-1,-1,
              JCPrimitiveTypeTree.class, 10,10,14,
              JmlBlock.class, 19,19,100,

              JmlStatementSpec.class, 25, 25, 90, 
              JmlMethodSpecs.class, 34, 34, 90,
              JmlSpecificationCase.class, 34,34,90,
              JmlModifiers.class, -1,-1,-1,

              RecommendsClause.Node.class, 34,34, 76,
              JCLiteral.class, 45, 45, 49,
              JCIdent.class, 55,55,75,

              JmlMethodClauseExpr.class, 77,77,90,
              JCLiteral.class, 85,85,89,
              JCExpressionStatement.class, 94,94,98,
              JCMethodInvocation.class, 94,95,97,
              JCIdent.class, 94,94,95
        );
    }
    
    @Test
    public void testRequires() {
        checkCompilationUnit("class A { /*@ requires true; */ void m(int i) {}}",
                JmlCompilationUnit.class, 0,0,49,
                JmlClassDecl.class, 0,0,49,
                JmlModifiers.class, -1,-1,-1,
                JmlMethodDecl.class, 32,37,48,

                JmlMethodSpecs.class, 14,14,28,
                JmlSpecificationCase.class, 14,14,28,
                JmlModifiers.class, -1,-1,-1,
                JmlMethodClauseExpr.class, 14,14,28,
                JCLiteral.class, 23,23,27,
                
                JmlModifiers.class, -1,-1,-1,
                JCPrimitiveTypeTree.class, 32,32,36,
                // The method name is not an AST
                JmlVariableDecl.class, 39,43,44,
                JmlModifiers.class, -1,-1,-1,
                JCPrimitiveTypeTree.class, 39,39,42,
                // The parameter name is a Name, not an AST
                JmlBlock.class, 46,46,48
                );
    }
    
    @Test
    public void testEnsures() {
        checkCompilationUnit("class A { /*@ ensures true; */ void m() {}}",
                JmlCompilationUnit.class, 0,0,43,
                JmlClassDecl.class, 0,0,43,
                JmlModifiers.class, -1,-1,-1,
                JmlMethodDecl.class, 31,36,42,

                JmlMethodSpecs.class, 14,14,27,
                JmlSpecificationCase.class, 14,14,27,
                JmlModifiers.class, -1,-1,-1,
                JmlMethodClauseExpr.class, 14,14,27,
                JCLiteral.class, 22,22,26,
                
                JmlModifiers.class, -1,-1,-1,
                JCPrimitiveTypeTree.class, 31,31,35,
                // The method name is a Name, not an AST
                JmlBlock.class, 40,40,42
                );
        
    }
    
    @Test
    public void testCallable() {
        checkCompilationUnit("class A { /*@ callable \\nothing   ; */ void m() {}}",
                JmlCompilationUnit.class, 0,0,51,
                JmlClassDecl.class, 0,0,51,
                JmlModifiers.class, -1,-1,-1,
                JmlMethodDecl.class, 39,44,50, // FIXME - specs are not inside the method decl
                
                JmlMethodSpecs.class, 14,14,35,
                JmlSpecificationCase.class, 14,14,35,
                JmlModifiers.class, -1,-1,-1,
                JmlMethodClauseCallable.class, 14,14,35,
                JmlSingleton.class, 23,23,31,
                
                JmlModifiers.class, -1,-1,-1,
                JCPrimitiveTypeTree.class, 39,39,43,
                JmlBlock.class, 48,48,50
                );        
    }
    
    @Test
    public void testCallable2() {
        checkCompilationUnit("class A { /*@ callable \\everything; */ void m() {}}",
                JmlCompilationUnit.class, 0,0,51,
                JmlClassDecl.class, 0,0,51,
                JmlModifiers.class, -1,-1,-1,
                JmlMethodDecl.class, 39,44,50, // FIXME - specs are not inside the method decl
                
                JmlMethodSpecs.class, 14,14,35,
                JmlSpecificationCase.class, 14,14,35,
                JmlModifiers.class, -1,-1,-1,
                JmlMethodClauseCallable.class, 14,14,35,
                JmlSingleton.class, 23,23,34,
                
                JmlModifiers.class, -1,-1,-1,
                JCPrimitiveTypeTree.class, 39,39,43,
                JmlBlock.class, 48,48,50
                );
    }
    
    // The harness tests test that the test routines report errors as expected (and, for example, do not crash)
    // Some variations are present to fill out test coverage
    
    // FIXME - compare to harness tests in parseErrors
    @Test
    public void harness1() {
        noExtraPrinting = true;
        checkParseFailure("Insufficient number of nodes listed: expected 1, was 3",
                "class A {}",
                JmlCompilationUnit.class, 0,0,10
                );
    }
    
    @Test
    public void harness2() {
        noExtraPrinting = true;
        checkParseFailure("Class not matched at token 0 expected:<class org.jmlspecs.openjml.JmlTree$JmlClassDecl> but was:<class org.jmlspecs.openjml.JmlTree$JmlCompilationUnit>",
                "class A {}",
                JmlClassDecl.class, 0,0,10,
                JmlModifiers.class, -1,-1,-1
                );
    }
    
    @Test
    public void harness3() {
        noExtraPrinting = true;
        checkParseFailure("Too many expected nodes listed expected:<16> but was:<12>",
                "class A {}",
                JmlCompilationUnit.class, 0,0,10,
                JmlClassDecl.class, 0,0,10,
                JmlModifiers.class, -1,-1,-1,
                JmlModifiers.class, -1,-1,-1
                );
    }
    
    @Test
    public void harness4a() {
        try {
            noExtraPrinting = true;
            checkParseFailure("ZZZ",
                    "class A {}",
                    JmlCompilationUnit.class, 0,0,10,
                    JmlClassDecl.class, 0,0,10
                    );
        } catch (AssertionError a) {
            org.junit.Assert.assertEquals("Test failure", 
                    "Failure message was incorrect in checkCompilationUnitFailure expected:<[ZZZ]> but was:<[Insufficient number of nodes listed: expected 2, was 3]>",
                    a.getMessage());
        }
    }
    
    @Test
    public void harness4b() {
        try {
            noExtraPrinting = true;
            checkParseFailure("",
                    "class A {}",
                    JmlCompilationUnit.class, 0,0,10,
                    JmlClassDecl.class, 0,0,10,
                    JmlModifiers.class, -1,-1,-1
                    );
        } catch (AssertionError a) {
            org.junit.Assert.assertEquals("Test failure", "Test Harness failed to report an error", a.getMessage());
        }
    }
    
    @Test
    public void harness4c() {
        var savedout = out;
        out = tempout;
        try {
            print = true;
            checkCompilationUnit(
                    "class A {}",
                    JmlCompilationUnit.class, 0,0,10,
                    JmlClassDecl.class, 0,0,10,
                    JmlModifiers.class, -1,-1,-1
                    );
        } finally {
            out = savedout;
        }
    }
    
    @Test
    public void harness4d() {
        var savedout = out;
        try {
            out = tempout;
            checkParseFailure("Insufficient number of nodes listed: expected 2, was 3",
                    "class A {}",
                    JmlCompilationUnit.class, 0,0,10,
                    JmlClassDecl.class, 0,0,10
                    );
        } finally {
            out = savedout;
        }
    }

    @Test
    public void harness4e() {
        var savedout = out;
        try {
            out = tempout;
            print = true; noExtraPrinting = true;
            checkParseFailure("Insufficient number of nodes listed: expected 2, was 3",
                    "class A {}",
                    JmlCompilationUnit.class, 0,0,10,
                    JmlClassDecl.class, 0,0,10
                    );
        } finally {
            out = savedout;
        }
    }

    @Test
    public void harness5() {
        noExtraPrinting = true;
        checkParseFailure("Class not matched at token 0 expected:<0> but was:<class org.jmlspecs.openjml.JmlTree$JmlCompilationUnit>",
                "class A {}",
                0,0,10
                );
    }
    
    @Test
    public void harness6() {
        noExtraPrinting = true;
        checkParseFailure("Start position for token 0 expected:<-100> but was:<0>",
                "class A {}",
                JmlCompilationUnit.class, -100,0,10,
                JmlClassDecl.class, 0,0,10,
                JmlModifiers.class, -1,-1,-1
                );
    }
    
    @Test
    public void harness7() {
        noExtraPrinting = true;
        checkParseFailure("Preferred position for token 0 expected:<-100> but was:<0>",
                "class A {}",
                JmlCompilationUnit.class, 0,-100,10,
                JmlClassDecl.class, 0,0,10,
                JmlModifiers.class, -1,-1,-1
                );
    }
    
    @Test
    public void harness8() {
        noExtraPrinting = true;
        checkParseFailure("End position for token 0 expected:<-100> but was:<10>",
                "class A {}",
                JmlCompilationUnit.class, 0,0,-100,
                JmlClassDecl.class, 0,0,10,
                JmlModifiers.class, -1,-1,-1
                );
    }
    
    @Test
    public void harness9() {
        noExtraPrinting = true;
        checkParseFailure("Start position for token 0 expected:<-100> but was:<0>",
                "class A {}",
                JmlCompilationUnit.class, -100,10,
                JmlClassDecl.class, 0,0,10,
                JmlModifiers.class, -1,-1,-1
                );
    }
    
    @Test
    public void harness10() {
        noExtraPrinting = true;
        checkParseFailure("End position for token 0 expected:<-100> but was:<10>",
                "class A {}",
                JmlCompilationUnit.class, 0,-100,
                JmlClassDecl.class, 0,0,10,
                JmlModifiers.class, -1,-1,-1
                );
    }
    
    @Test
    public void harness11() {
        noExtraPrinting = true;
        checkParseFailure("Preferred position for token 0 expected:<-100> but was:<0>",
                "class A {}",
                JmlCompilationUnit.class, -100,
                JmlClassDecl.class, 0,0,10,
                JmlModifiers.class, -1,-1,-1
                );
    }
    // FIXME - add all other constructs: multiple classes, interfaces, enums, extends, implements, declarations, clauses, method constructs, method clauses, nowarn

}
