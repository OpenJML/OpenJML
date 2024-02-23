package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.ext.RecommendsClause;
import org.jmlspecs.openjmltest.ParseBase;
import org.junit.Test;

import com.sun.tools.javac.tree.JCTree.*;


/** Tests that the parser creates the correct tokens for some simple
 * compilation unit tests, in particular for refines and import statements.
 * @author David Cok
 *
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class compilationUnit extends ParseBase {

    @Override
    public void setUp() throws Exception {
//        jmldebug = true;
        super.setUp();
    }

  
    /** Quickie test of some pure Java code */
    @Test
    public void testSomeJava() {
        checkCompilationUnit("package t; \nclass A{}",
                JmlCompilationUnit.class,0,
                JCPackageDecl.class, 0,
                JCIdent.class, 8,
                JmlClassDecl.class, 12,
                JmlModifiers.class, -1);
        checkMessages();
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
        checkMessages();
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
        checkMessages();
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
        checkMessages();
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
        checkMessages();
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
        checkMessages();
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
        checkMessages();
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
        checkMessages();
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
        checkMessages();
    }

    /** Tests parsing a modifier */
    @Test
    public void testAnnotation2() {
        checkCompilationUnit("/*@ pure */ class A {}"
        ,JmlCompilationUnit.class, 0,0,22
        ,JmlClassDecl.class, 4,12,22
        ,JmlModifiers.class, 4,4,11 // FIXME - would like this to be 8
        );
        checkMessages();
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
        checkMessages();
    }
    
    //  @Test -
    public void testRefining2() {
        checkCompilationUnit("class A { void m() { /*@        recommends true else NullPointerException; ensures true; */ m(); }}",
              JmlCompilationUnit.class, 0,0,99,
              JmlClassDecl.class, 0,0,99,
              JmlModifiers.class, -1,-1,-1,
              JmlMethodDecl.class, 10,15,98,
              JmlModifiers.class, -1,-1,-1,
              JCPrimitiveTypeTree.class, 10,10,14,
              JmlBlock.class, 19,19,98,

              JmlStatementSpec.class, 32, 32, 88, 
              JmlMethodSpecs.class, 32, 32, 88,
              JmlSpecificationCase.class, 32,32,88,
              JmlModifiers.class, -1,-1,-1,

              RecommendsClause.Node.class, 32,32, 74,
              JCLiteral.class, 43, 43, 47,
              JCIdent.class, 53,53,73,

              JmlMethodClauseExpr.class, 75,75,88,
              JCLiteral.class, 83,83,87,
              JCExpressionStatement.class, 92,92,96,
              JCMethodInvocation.class, 92,93,95,
              JCIdent.class, 92,92,93
        );
        checkMessages();
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
        
        checkMessages();
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
        
        checkMessages();
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
        checkMessages();
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
        
        checkMessages();
    }
    
    // FIXME - add all other constructs: multiple classes, interfaces, enums, extends, implements, declarations, clauses, method constructs, method clauses, nowarn

}
