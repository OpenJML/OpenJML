package org.jmlspecs.openjmltest.testcases;

import static com.sun.tools.javac.parser.Tokens.*;
import static com.sun.tools.javac.parser.Tokens.TokenKind.*;
import static org.jmlspecs.openjml.JmlTokenKind.*;

import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjmltest.JmlTestCase;
import org.jmlspecs.openjmltest.TestJavaFileObject;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.ParameterizedWithNames;
import org.junit.runners.Parameterized.Parameters;

import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.parser.ParserFactory;
import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.parser.ScannerFactory;
import com.sun.tools.javac.parser.Tokens;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Log;

import static org.junit.Assert.*;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

@RunWith(ParameterizedWithNames.class)
public class parser extends JmlTestCase {

    ParserFactory parserFactory;
    
    Test test;
    
    // TODO - do we need to collect and compare System.out,err
    
    /** Initializes a fresh parser for each test */
    @Override
    public void setUp() throws Exception {
        super.setUp(); // Sets up a main program, diagnostic collector
        parserFactory = ParserFactory.instance(context);
    }

//    /** This is a helper routine to check tests that are supposed to issue
//     * JUnit test failures.
//     * 
//     * @param failureMessage The expected JUnit failure message
//     * @param s The string to parse
//     * @param list The tokens expected
//     * @param positions The expected start and end positions for each token
//     * @param numErrors The expected number of scanning errors
//     */
//    //@ requires positions != null && list != null ==> positions.length == list.length*2;
//    public void helpFailure(String failureMessage, String s, ITokenKind[] list, /*@nullable*/ int[] positions, int numErrors) {
//        boolean failed = false;
//        try {
//            helpScanner(s,list,positions,numErrors);
//        } catch (AssertionError a) {
//            failed = true;
//            assertEquals("Failure report wrong",failureMessage,a.getMessage());
//        }
//        if (!failed) fail("Test harness failed to report an error");
//    }


//    /** This scans the input string and checks whether the tokens obtained
//     * match those in the list array and whether the positions found
//     * match those in the positions array and whether the number of
//     * errors found is 0.  The positions array contains a start and end position
//     * for each token.
//     */
//    public void helpScanner(String s, ITokenKind[] list, int[] positions) {
//        helpScanner(s,list,positions,0);
//    }
    
    @Parameters
    static public Test[] datax() {
        return tests;
    }

    public parser(Test test) {
        
    }
    
    public static class Finder extends JmlTreeScanner {
        
        Class<?> clazz;
        JCTree done = null;
        
        public Finder(Class<?> clazz) {
            this.clazz = clazz;
        }
        
        public void scan(JCTree tree) {
            if (done != null) return;
            if (tree.getClass() == clazz) { done = tree; return; }
            if(tree!=null) tree.accept(this);
        }
        
        static JCTree find(Class<?> clazz, JCTree tree) {
            Finder f = new Finder(clazz);
            tree.accept(f);
            return f.done;
        }

    }

    public void helpParser(boolean compunit, String s, Class<?> clazz, int[] positions, int numErrors) {
        try {
            Log log = Log.instance(context);
            log.useSource(new TestJavaFileObject(s) );
            JmlParser parser = (JmlParser)parserFactory.newParser(s, false, true, true);
            JCTree result;
            if (compunit) {
                JCCompilationUnit tree = parser.parseCompilationUnit();
                result = Finder.find(clazz,tree);
                if (collector.getDiagnostics().size() != numErrors) {
                    printDiagnostics();
                    fail("Saw errors: expected " + numErrors 
                                            + " actual " + collector.getDiagnostics().size());
                }
                assertTrue("found node", result != null);
                assertEquals("start position-A", positions[0], result.getStartPosition());
                assertEquals("start position-B", positions[0], parser.getStartPos(result));
                assertEquals("pref position", positions[1], result.getPreferredPosition());
                assertEquals("end position-A", positions[2], result.getEndPosition(tree.endPositions));
                assertEquals("end position-B", positions[2], parser.getEndPos(result));
            } else {
                JCExpression tree = parser.parseExpression();
                result = Finder.find(clazz,tree);
                if (collector.getDiagnostics().size() != numErrors) {
                    printDiagnostics();
                    fail("Saw errors: expected " + numErrors 
                                            + " actual " + collector.getDiagnostics().size());
                }
                assertTrue("found node", result != null);
                assertEquals("start position-A", positions[0], result.getStartPosition());
                assertEquals("start position-B", positions[0], parser.getStartPos(result));
                assertEquals("pref position", positions[1], result.getPreferredPosition());
                assertEquals("end position", positions[2], parser.getEndPos(result));
            }
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    ////////////////////////////////////////////////////////////////////////
    
    public static class Test {
        boolean compunit;
        String input;
        Class<?> clazz;
        int[] positions;
        int numerrors;
        
        public Test(boolean cu, String input, Class<?> clazz, int[] positions, int numerrors) {
            this.compunit = cu;
            this.input = input;
            this.clazz = clazz;
            this.positions = positions;
            this.numerrors = numerrors;
        }
    }
    
    static Test[] tests = new Test[]{
       new Test(false,"2 + (\\forall int x,y; 0 <= x; y == x) + 7", JmlQuantifiedExpr.class, new int[]{0,0,0}, 0),
       new Test(true,"public class A { int i = 2 + (\\forall int x,y; 0 <= x; y == x) + 7; }", JmlQuantifiedExpr.class, new int[]{0,0,0}, 0),
    };
    
    @org.junit.Test
    public void run() {
        helpParser(test.compunit, test.input, test.clazz, test.positions, test.numerrors);
    }

}
