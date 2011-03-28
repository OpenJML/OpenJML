package tests;

import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlImport;

import com.sun.tools.javac.tree.JCTree.*;


/** Tests that the parser creates the correct tokens for some simple
 * compilation unit tests, in particular for refines and import statements.
 * @author David Cok
 *
 */

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
                JmlCompilationUnit.class,2,
                JCErroneous.class, 4,
                JmlClassDecl.class, 24,
                JCModifiers.class, -1);
        checkMessages("/TEST.java:1: class, interface, or enum expected",5);
    }


    /** Tests a star import */
    public void testImports() {
        checkCompilationUnit("import java.io.*;  class A{}",
                JmlCompilationUnit.class, 0,0,28,
                JmlImport.class, 0,0,17,
                JCFieldAccess.class, 7,14,16,
                JCFieldAccess.class, 7,11,14,
                JCIdent.class, 7,7,11,
                JmlClassDecl.class, 19,19,28,
                JCModifiers.class, -1,-1,-1);
        checkMessages();
    }
    
    /** Tests a static star import */
    public void testImports2() {
        checkCompilationUnit("import static java.io.*;  class A{}",
                JmlCompilationUnit.class, 0,0,35,
                JmlImport.class, 0,0,24,
                JCFieldAccess.class, 14,21,23,
                JCFieldAccess.class, 14,18,21,
                JCIdent.class, 14,14,18,
                JmlClassDecl.class, 26,26,35,
                JCModifiers.class, -1,-1,-1);
        checkMessages();
    }
    
    /** Tests a static non-star import */
    public void testImports3() {
        checkCompilationUnit("import static java.io.File;  class A{}",
                JmlCompilationUnit.class, 0,0,38,
                JmlImport.class, 0,0,27,
                JCFieldAccess.class, 14,21,26,
                JCFieldAccess.class, 14,18,21,
                JCIdent.class, 14,14,18,
                JmlClassDecl.class, 29,29,38,
                JCModifiers.class, -1,-1,-1);
        checkMessages();
    }
    
    /** Tests a non-star import with modifier */
    public void testImports4() {
        checkCompilationUnit("import java.io.File;  public class A{}",
                JmlCompilationUnit.class, 0,0,38,
                JmlImport.class, 0,0,20,
                JCFieldAccess.class, 7,14,19,
                JCFieldAccess.class, 7,11,14,
                JCIdent.class, 7,7,11,
                JmlClassDecl.class, 22,29,38,
                JCModifiers.class, 22,22,28);
        checkMessages();
    }
    
    /** Tests a non-star import with 2 modifiers */
    public void testImports5() {
        checkCompilationUnit("import java.io.File;  public protected class A{}",
                JmlCompilationUnit.class, 0,0,48,
                JmlImport.class, 0,0,20,
                JCFieldAccess.class, 7,14,19,
                JCFieldAccess.class, 7,11,14,
                JCIdent.class, 7,7,11,
                JmlClassDecl.class, 22,39,48,
                JCModifiers.class, 22,22,38);
        checkMessages();
    }
    
    /** Tests parsing an annotation */
    public void testAnnotation() {
        checkCompilationUnit("@org.jmlspecs.annotation.Pure class A {}",
                JmlCompilationUnit.class, 0,0,40,
                JmlClassDecl.class, 0,30,40,
                JCModifiers.class, 0,0,29,
                JCAnnotation.class, 0,0,29,
                JCFieldAccess.class, 1,24,29,
                JCFieldAccess.class, 1,13,24,
                JCFieldAccess.class, 1,4,13,
                JCIdent.class, 1,1,4
                              );
        checkMessages();
    }

    /** Tests parsing an annotation and modifier */
    public void testAnnotation1() {
        checkCompilationUnit("@org.jmlspecs.annotation.Pure public class A {}",
                JmlCompilationUnit.class, 0,0,47,
                JmlClassDecl.class, 0,37,47,
                JCModifiers.class, 0,0,36,
                JCAnnotation.class, 0,0,29,
                JCFieldAccess.class, 1,24,29,
                JCFieldAccess.class, 1,13,24,
                JCFieldAccess.class, 1,4,13,
                JCIdent.class, 1,1,4
                              );
        checkMessages();
    }

    /** Tests parsing an annotation and modifier and annotation */
    public void testAnnotation1a() {
        checkCompilationUnit("@org.jmlspecs.annotation.Pure public @org.jmlspecs.annotation.NonNull class A {}",
                JmlCompilationUnit.class, 0,0,80,
                JmlClassDecl.class, 0,70,80,
                JCModifiers.class, 0,0,69,
                JCAnnotation.class, 0,0,29,
                JCFieldAccess.class, 1,24,29,
                JCFieldAccess.class, 1,13,24,
                JCFieldAccess.class, 1,4,13,
                JCIdent.class, 1,1,4,
                JCAnnotation.class, 37,37,69,
                JCFieldAccess.class, 38,61,69,
                JCFieldAccess.class, 38,50,61,
                JCFieldAccess.class, 38,41,50,
                JCIdent.class, 38,38,41
                              );
        checkMessages();
    }

    /** Tests parsing a traditional JML annotation */
    public void testAnnotation2() {
        checkCompilationUnit("/*@ pure */ class A {}",
        JmlCompilationUnit.class, 2,2,22, // FIXME - start,preferred positions
        JmlClassDecl.class, 4,12,22,
        JCModifiers.class, 4,4,10, // FIXME - end
        JCAnnotation.class, 4,4,8,
        JCFieldAccess.class, 4,4,8,
        JCFieldAccess.class, 4,4,8,
        JCFieldAccess.class, 4,4,8,
        JCIdent.class, 4,4,8
                      );
        checkMessages();
    }
    
    // FIXME - add all other constructs: multiple classes, interfaces, enums, extends, implements, declarations, clauses, method constructs, method clauses, nowarn

}
