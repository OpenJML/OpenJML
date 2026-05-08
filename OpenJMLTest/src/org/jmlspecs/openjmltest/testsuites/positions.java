package org.jmlspecs.openjmltest.testsuites;

import java.util.Arrays;
import org.openjml.MockJavaFileObject;

import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjmltest.JmlTestSuite;

import static org.junit.Assert.*;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.ParserFactory;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Log;

// This test class checks that the parser produces correct positions for the various parsed 
// constructs. Each one should have a start position, end position, and a preferred position.
// The first two should span the construct from beginning to end. Note that the end position is
// one beyond the textual end; also these are character positions from the beginning of the file,
// with 0 being the first character. The 'preferred position' is the location to use when a single
// character is wanted. It is often the same as the start position, but in some case not; for example,
// for a binary operation, the preferred position is the location of the operator.

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class positions extends JmlTestSuite {

    @Rule public TestName testname = new TestName();

    ParserFactory parserFactory;
    
    Test test;
    
    /** Initializes a fresh parser for each test */
    @Override
    public void setUp() throws Exception {
        super.setUp(); // Sets up a main program, diagnostic collector
        main.postOptionProcessing();
        try {
            // Makes sure that components are instantiated without circularity
            com.sun.tools.javac.main.JmlCompiler.instance(context);
            parserFactory = ParserFactory.instance(context);
        } catch (Exception e) {
            // CATASTROPHIC INTERNAL BUG
            e.printStackTrace(this.out);
        }
    }

    @Parameters
    static public java.util.Collection<Object[]> datax() {
        return Arrays.asList(tests);
    }
    
    public positions(Test test) {
        this.test = test;
    }
    
    public static class Print extends JmlTreeScanner {
        java.io.PrintStream out;
        
        public Print(java.io.PrintStream out) {
            this.out = out;
        }
        
        public void scan(JCTree tree) {
            if(tree!=null) {
                out.println(tree.getClass());
                tree.accept(this);
            }
        }
        
        static void print(JCTree tree, java.io.PrintStream out) {
            tree.accept(new Print(out));
        }
    }

    public static class Finder extends JmlTreeScanner {
        
        Class<?> clazz;
        JCTree done = null;
        
        public Finder(Class<?> clazz) {
            this.clazz = clazz;
        }
        
        public void scan(JCTree tree) {
            if (done != null) return;
            if (tree == null) return;
            if (tree.getClass() == clazz) { done = tree; return; }
            tree.accept(this);
        }
        
        static JCTree find(Class<?> clazz, JCTree tree) {
            Finder f = new Finder(clazz);
            tree.accept(f);
            return f.done;
        }
    }

    public void helpParser(boolean compunit, String markedString, Class<?> clazz, int numErrors, String[] messages) {
        boolean intentionalError = numErrors < 0;
        numErrors = Math.abs(numErrors);
        try {
            int startpos = markedString.indexOf('#');
            int prefpos = markedString.indexOf('#',startpos+1)-1;
            int endpos = markedString.indexOf('#',prefpos+2)-2;
            int endpos2 = markedString.indexOf('#',endpos+3)-3;
            if (endpos2 < 0) endpos2 = endpos;
            String testString = markedString.replaceAll("#","");
            Log log = Log.instance(context);
            log.useSource(new MockJavaFileObject(testString));
            JmlParser parser = (JmlParser)parserFactory.newParser(testString, false, true, true);
            JCTree result;
            JCTree ztree = null;
            int observedErrors = 0;
            try {
                if (compunit) {
                    JCCompilationUnit tree = parser.parseCompilationUnit();
                    assertTrue("parse failure", tree != null);
                    result = Finder.find(clazz,tree);
                    assertEquals("end position-A", endpos, result.getEndPosition(tree.endPositions));
                    ztree = tree;
                } else {
                    parser.getScanner().setJml(true);
                    JCExpression tree = parser.parseExpression();
                    assertTrue("parse failure", tree != null);
                    ztree = tree;
                }
                observedErrors = collector.getDiagnostics().size();

                result = Finder.find(clazz,ztree);
                // printDiagnostics(); // Uncomment to debug test failures
                assertTrue("failed to find node", result != null);
                assertEquals("start position-A", startpos, result.getStartPosition());
                assertEquals("start position-B", startpos, parser.getStartPos(result));
                assertEquals("pref position", prefpos, result.getPreferredPosition());
                assertEquals("end position-B", endpos2, parser.getEndPos(result));
                assertEquals("Wrong number of errors:", numErrors, observedErrors);

                for (int i = 0; i < observedErrors; i++) {
                    String msg = collector.getDiagnostics().get(i).toString();
                    assertEquals(messages[i], msg);
                }

            } catch (AssertionError e) {
                if (intentionalError) {
                    assertEquals(e.getMessage(), "Wrong number of errors: expected:<1> but was:<0>");
                } else {
                    this.out.println(clazz + " " + startpos + " " + prefpos + " " + endpos);
                    this.out.println(testString);
                    if (e.getMessage().contains("failed to find")) Print.print(ztree, this.out);
                    throw e;
                }
            }
        } catch (Exception e) {
            e.printStackTrace(this.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    ////////////////////////////////////////////////////////////////////////
    static int count = 0;
    
    public static class Test {
        int id;           // index
        boolean compunit; // true->compilation unit; false->expression
        String input;     // text to be parsed
        Class<?> clazz;   // the class of the AST text enclosed in ##...#
        int numerrors;    // the number of errors expected
        String[] output;
        
        public Test(boolean cu, String input, Class<?> clazz, int numerrors, String... output) {
            this.id = count++;
            this.compunit = cu;
            this.input = input;
            this.clazz = clazz;
            this.numerrors = numerrors;
            this.output = output;
        }
        
        public String toString() {
            return "" + id;
        }
    }
    
    // Put the # characters just before the start and pref and end positions, but note that
    // the end position is one after the end of the parser construct, so put the # just after
    // the end of the parser string
    static Object[][] tests = new Object[][]{
        { new Test(false,"2 + (##~ 1#) + 7", JCUnary.class, 0)},
        { new Test(false," (#2 #+ 1#) ", JCBinary.class, 0)},
        { new Test(false," (#true #? 1 : 2#) ", JCConditional.class, 0)},
        { new Test(false," (#true #==> false#) ", JmlBinary.class, 0)},
        { new Test(false,"2 + (##\\forall int x,y; 0 <= x; y == x#) + 7", JmlQuantifiedExpr.class, 0)},
        { new Test(true,"public class A { //@ ghost boolean i = ##true# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost int i = ##70# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost long i = ##70L# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost char i = ##'c'# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost String i = ##\"asd\"# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost double i = ##70.0# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost double i = ##70.0e1# ;\n }", JCLiteral.class, 0)},
        { new Test(true,"public class A { //@ ghost int i = 2 + (##\\forall int x,y; 0 <= x; y == x#) + 7;\n }", JmlQuantifiedExpr.class, 0)},
        { new Test(true,"public class A { //@ assignable #a#[ *]#;\n void m(){}}", JCArrayAccess.class, 0)},
        { new Test(true,"public class A { //@ assignable #a#[ 2 .. 4]#;\n void m(){}}", JCArrayAccess.class, 0)},
        { new Test(true,"public class A { //@ assignable #a#[ 2 .. ]#;\n void m(){}}", JCArrayAccess.class, 0)},
        { new Test(true,"public class A {  void m(){ class Z { void q() { //@ ghost int s = 0; \n  //@ ##assert true#;# \n}}}}", 
                JmlStatementExpr.class, 0)},
        { new Test(true,"public class A {  void m(){ class Z { void q() { //@ ghost int s = 0; \n  //@ ##assert true# \n}}}}", JmlStatementExpr.class, 1
                ,"""
                 /TEST.java:2: warning: Inserting missing semicolon at the end of a assert statement
                   //@ assert true\s
                                   ^""")},
        { new Test(false,"2 + (##~ 1#) +", JCUnary.class, 1,
                """
                /TEST.java:1: error: reached end of file while parsing
                2 + (~ 1) +
                           ^""")},

//        FIXME
//        { new Test(true,"public class A { //@ assignable ##abc# ;\n void m(){}}", JCIdent.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##ab . c# ;\n void m(){}}", JCFieldAccess.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##ab . *# ;\n void m(){}}", JCFieldAccess.class, 0)},
////        { new Test(true,"public class A { //@ assignable ##\\nothing#;\n", JmlStoreRefKeyword.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##\\everything#;\n", JmlStoreRefKeyword.class, 0)},
//        { new Test(true,"public class A { //@ assignable ##a, ab . *# ;\n void m(){}}", JmlStoreRefListExpression.class, 0)},
        
        // harness failures
        { new Test(false,"2 + (##~ 1#) + 7", JCUnary.class, -1)},
        { new Test(true,"public class A { //@ ghost boolean i = ##true# ;\n }", JCLiteral.class, -1)},
    };
    
    
    @org.junit.Test
    public void run() {
        helpParser(test.compunit, test.input, test.clazz, test.numerrors, test.output);
    }

}
