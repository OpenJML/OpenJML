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
// TODO - needs tests of model imports
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
        checkCompilationUnit("@org.jmlspecs.annotation.Pure class A {}",
                JmlCompilationUnit.class, 0,
                JmlClassDecl.class, 30,
                JCModifiers.class, 0, // TODO - was 30?
                JCAnnotation.class, 0,
                JCFieldAccess.class, 24,
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
        JCModifiers.class, -1, // TODO - should be 12?
        JCAnnotation.class, 4,
        JCFieldAccess.class, 4,
        JCFieldAccess.class, 4,
        JCFieldAccess.class, 4,
        JCIdent.class, 4
                      );
        checkMessages();
    }

}
