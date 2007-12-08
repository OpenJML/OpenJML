package tests;

import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlRefines;

import com.sun.tools.javac.tree.JCTree.*;



public class compilationUnit extends ParseBase {

    @Override
    public void setUp() throws Exception {
//        noCollectDiagnostics = true;
//        jmldebug = true;
        super.setUp();
    }

  
    /** Quickie test of some pure Java code */
    public void testSomeJava() {
        checkCompilationUnit("package t; \nclass A{}",
                JmlCompilationUnit.class,0,
                JCIdent.class, 8,
                JmlClassDecl.class, 12,
                JCModifiers.class, -1);
        checkMessages();
    }
    
    /** One refines clause with no package or imports */
    public void testRefines() {
        checkCompilationUnit("/*@ refines \"A.xxx\"; */ class A{}",
                JmlCompilationUnit.class,4,
                JmlRefines.class, 4,
                JmlClassDecl.class, 24,
                JCModifiers.class, -1);
        checkMessages();
    }

    /** Package and refines clauses */
    public void testRefines2() {
        checkCompilationUnit("package t; /*@ refines \"A.xxx\"; */ class A{}",
                JmlCompilationUnit.class,0,
                JCIdent.class, 8,
                JmlRefines.class, 15,
                JmlClassDecl.class, 35,
                JCModifiers.class, -1);
        checkMessages();
    }

    /** Refines before package */   // TODO - this error message could be improved
    public void testRefines2a() {
        checkCompilationUnit("/*@ refines \"A.xxx\"; */ package t; class A{}",
                JmlCompilationUnit.class,4,
                JmlRefines.class, 4,
                JCErroneous.class, 24,
                JmlClassDecl.class, 35,
                JCModifiers.class, -1);
        checkMessages("/TEST.java:1: class, interface, or enum expected",25);
    }

    /** Package and two refines clauses */
    public void testRefines3() {  // TODO - could improve by having the second message first
        checkCompilationUnit("package t; /*@ refines \"A.xxx\"; */\n /*@ refines \"B.xxx\"; */ class A{}",
                JmlCompilationUnit.class,0,
                JCIdent.class, 8,
                JmlRefines.class, 15,
                JmlClassDecl.class, 60,
                JCModifiers.class, -1);
        checkMessages(
                "/TEST.java:2: A compilation unit may have at most one refines clause",6);
    }

    /** Package, refines, import, refines clauses */
    public void testRefines4() {
        checkCompilationUnit("package t; /*@ refines \"A.xxx\"; */\n import java.io.*; /*@ refines \"B.xxx\"; */ class A{}",
                JmlCompilationUnit.class,0,
                JCIdent.class, 8,
                JmlRefines.class, 15,
                JmlImport.class, 36,
                JCFieldAccess.class, 50,
                JCFieldAccess.class, 47,
                JCIdent.class, 43,
                JmlClassDecl.class, 78,
                JCModifiers.class, -1);
        checkMessages(
                "/TEST.java:2: Refines declarations must precede all import declarations and follow any package declaration",24,
                "/TEST.java:2: A compilation unit may have at most one refines clause",24);
    }

    /** Refines without a string */
    public void testRefines5() {
        parseCompilationUnit("package t; /*@ refines ; */ class A{}");
        checkMessages("/TEST.java:1: A refines declaration must contain a string literal",24);
    }

    /** Refines with no string or semicolon */
    public void testRefines6() {
        parseCompilationUnit("package t; /*@ refines  */  class A{}");
        checkMessages("/TEST.java:1: A refines declaration must contain a string literal",25);
    }

    /** Refines with no string or semicolon */
    public void testRefines7() {
        parseCompilationUnit("package t; /*@ refines \"X.spec\" */  class A{}");
        checkMessages("/TEST.java:1: A refines statement needs to be ended by a semicolon",33);
    }

    /** Tests a star import */
    public void testImports() {
        checkCompilationUnit("import java.io.*;  class A{}",
                JmlCompilationUnit.class, 0,
                JmlImport.class, 0,
                JCFieldAccess.class, 14,
                JCFieldAccess.class, 11,
                JCIdent.class, 7,
                JmlClassDecl.class, 19,
                JCModifiers.class, -1);
        checkMessages();
    }
    
    /** Tests a static star import */
    public void testImports2() {
        checkCompilationUnit("import static java.io.*;  class A{}",
                JmlCompilationUnit.class, 0,
                JmlImport.class, 0,
                JCFieldAccess.class, 21,
                JCFieldAccess.class, 18,
                JCIdent.class, 14,
                JmlClassDecl.class, 26,
                JCModifiers.class, -1);
        checkMessages();
    }
    
    /** Tests a static non-star import */
    public void testImports3() {
        checkCompilationUnit("import static java.io.File;  class A{}",
                JmlCompilationUnit.class, 0,
                JmlImport.class, 0,
                JCFieldAccess.class, 21,
                JCFieldAccess.class, 18,
                JCIdent.class, 14,
                JmlClassDecl.class, 29,
                JCModifiers.class, -1);
        checkMessages();
    }
    
    /** Tests a non-star import */
    public void testImports4() {
        checkCompilationUnit("import static java.io.File;  class A{}",
                JmlCompilationUnit.class, 0,
                JmlImport.class, 0,
                JCFieldAccess.class, 21,
                JCFieldAccess.class, 18,
                JCIdent.class, 14,
                JmlClassDecl.class, 29,
                JCModifiers.class, -1);
        checkMessages();
    }
    
    /** Tests parsing an annotation */
    public void testAnnotation() {
        checkCompilationUnit("@org.jmlspecs.annotations.Pure class A {}",
                JmlCompilationUnit.class, 0,
                JmlClassDecl.class, 31,
                JCModifiers.class, 31,
                JCAnnotation.class, 0,
                JCFieldAccess.class, 25,
                JCFieldAccess.class, 13,
                JCFieldAccess.class, 4,
                JCIdent.class, 1
                              );
        checkMessages();
    }

    /** Tests parsing a traditional JML annotation */
    public void testAnnotation2() {
        checkCompilationUnit("/*@ pure */ class A {}",
        JmlCompilationUnit.class, 2,
        JmlClassDecl.class, 12,
        JCModifiers.class, 12,
        JCAnnotation.class, 4,
        JCFieldAccess.class, 4,
        JCFieldAccess.class, 4,
        JCFieldAccess.class, 4,
        JCIdent.class, 4
                      );
        checkMessages();
    }

}
