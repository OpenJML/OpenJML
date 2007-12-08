package tests;
import java.util.List;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.Parser;
import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.parser.Token;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Log;

import junit.framework.AssertionFailedError;


public class expressions extends ParseBase {

    /** Set this to true in tests which start out the scanner in jml mode
     * (avoiding the need to begin the test string with a JML comment annotation)
     */
    boolean jml;
    

    protected void setUp() throws Exception {
//        noCollectDiagnostics = true;
        super.setUp();
        jml = true;
    }

    // TODO - put in a few harness tests
    // TODO - test error messages
    public void helpFailure(String failureMessage, String s, Object ... list) {
        boolean failed = false;
        try {
            helpExpr(s,list);
        } catch (AssertionFailedError a) {
            failed = true;
            assertEquals("Failure report wrong",failureMessage,a.getMessage());
        }
        if (!failed) fail("Test Harness failed to report an error");
    }

    public void helpExpr(String s, Object... list) {
        try {
            Log.instance(context).useSource(new TestJavaFileObject(s));
            Scanner sc = sfac.newScanner(s);
            if (jml && sc instanceof JmlScanner) {
                ((JmlScanner)sc).setJml(jml);
            }
            Parser p = fac.newParser(sc,false,true);
            JCTree.JCExpression e = p.expression();
            List<JCTree> out = ParseTreeScanner.walk(e);
            int i = 0;
            int k = 0;
            if (print) {
                for (JCTree t: out) {
                    System.out.println(t.getClass() + " " + t.getPreferredPosition());
                }
            }
            if (print || d.getDiagnostics().size() != 0)
                printErrors();
            if (d.getDiagnostics().size() != 0) {
                fail("Saw unexpected errors");
            }
            if (out.size()*2 != list.length) {
                assertEquals("Incorrect number of nodes listed",list.length/2,out.size());
            }
            for (JCTree t: out) {
                assertEquals("Class not matched at token " + k, list[i++], t.getClass());
                assertEquals("Preferred position for token " + k, list[i++], t.getPreferredPosition());
                ++k;
            }
            if (sc.token() != Token.EOF) fail("Not at end of input");
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    public void helpExprErrors(String s, Object... list) {
        try {
            Log.instance(context).useSource(new TestJavaFileObject(s));
            Scanner sc = sfac.newScanner(s);
            if (jml && sc instanceof JmlScanner) {
                ((JmlScanner)sc).setJml(jml);
            }
            Parser p = fac.newParser(sc,false,true);
            p.expression();
            int i = 0;
            if (print || d.getDiagnostics().size() != list.length) printErrors();
            assertEquals("Saw wrong number of errors ",list.length,d.getDiagnostics().size());
            for (Diagnostic<? extends JavaFileObject> dd: d.getDiagnostics()) {
                assertEquals("Error message " + i,list[i++],dd.toString());
            }
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }


    /** Test scanning something very simple */
    public void testSomeJava() {
        jml = false;
        helpExpr("a",
                JCIdent.class ,0);
        helpExpr("aaa",
                JCIdent.class ,0);
    }

    /** Test scanning Java binary expression to check node positions */
    public void testBinary() {
        jml = false;
        helpExpr("aa+bbb",
                JCBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,3);
    }

    /** Test scanning JML equivalence expression */
    public void testJMLBinary1() {
        helpExpr("a <==> b",
                JmlBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7);
    }

    /** Test scanning JML inequivalence expression */
    public void testJMLBinary2() {
        helpExpr("a <=!=>b",
                JmlBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7);
    }

    /** Test scanning JML implies expression */
    public void testJMLBinary3() {
        helpExpr("a ==>  b",
                JmlBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7);
    }

    /** Test scanning JML reverse implies expression */
    public void testJMLBinary4() {
        helpExpr("a <==  b",
                JmlBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7);
    }

    /** Test JML left association for <==> */
    public void testJMLprecedence() {
        helpExpr("a <==> b <==> c <==> d",
                JmlBinary.class, 16,
                JmlBinary.class, 9,
                JmlBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7,
                JCIdent.class ,14,
                JCIdent.class ,21);
    }

    /** Test JML right association for ==> */
    public void testJMLprecedence1() {
        helpExpr("a ==>  b ==>  c ==>  d",
                JmlBinary.class, 2,
                JCIdent.class ,0,
                JmlBinary.class, 9,
                JCIdent.class ,7,
                JmlBinary.class, 16,
                JCIdent.class ,14,
                JCIdent.class ,21);
    }

    /** Test JML left association for <== */
    public void testJMLprecedence1a() {
        helpExpr("a <==  b <==  c <==  d",
                JmlBinary.class, 16,
                JmlBinary.class, 9,
                JmlBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7,
                JCIdent.class ,14,
                JCIdent.class ,21);
    }

    /** Test precedence between equiv and implies operators */
    public void testJMLprecedence2() {
        helpExpr("a ==>  b <==> c ==>  d",
                JmlBinary.class, 9,
                JmlBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7,
                JmlBinary.class, 16,
                JCIdent.class ,14,
                JCIdent.class ,21);
    }

    /** Test association of equiv operators */
    public void testJMLprecedence2a() {
        helpExpr("a <==> b <==> c <==> d",
                JmlBinary.class, 16,
                JmlBinary.class, 9,
                JmlBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7,
                JCIdent.class ,14,
                JCIdent.class ,21);
    }

    /** Test precedence between equivalence and Java operators */
    public void testJMLprecedence3() {
        helpExpr("a +    b <==> c ||   d",
                JmlBinary.class, 9,
                JCBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7,
                JCBinary.class, 16,
                JCIdent.class ,14,
                JCIdent.class ,21);
    }

    /** Test precedence between implies and Java operators */
    public void testJMLprecedence4() {
        helpExpr("a +    b ==>  c ||   d",
                JmlBinary.class, 9,
                JCBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7,
                JCBinary.class, 16,
                JCIdent.class ,14,
                JCIdent.class ,21);
    }

    /** Test precedence between equivalence and assignment, ternary operators */
    public void testJMLprecedence5() {
        helpExpr("a = b<==>bb ? c<=!=>cc : d<==>dd",
                JCAssign.class, 2,
                JCIdent.class ,0,
                JCConditional.class, 12,
                  JmlBinary.class, 5,
                    JCIdent.class ,4,
                    JCIdent.class ,9,
                  JmlBinary.class, 15,
                    JCIdent.class ,14,
                    JCIdent.class ,20,
                  JmlBinary.class, 26,
                    JCIdent.class ,25,
                    JCIdent.class ,30);
    }

    /** Test scanning \result expression */
    public void testResult() {
        helpExpr(" \\result + \\result",
                JCBinary.class, 9,
                JmlSingleton.class ,1,
                JmlSingleton.class ,11);
    }

    /** Test scanning \old expression */
    public void testOld() {
        helpExpr(" \\old(a+b)",
                JCMethodInvocation.class, 5,
                JmlFunction.class, 1,
                JCBinary.class, 7,
                JCIdent.class ,6,
                JCIdent.class ,8);
    }

    /** Test scanning \elemtype expression */
    public void testElemtype() {
        helpExpr(" \\elemtype(a+b)",
                JCMethodInvocation.class, 10,
                JmlFunction.class, 1,
                JCBinary.class, 12,
                JCIdent.class ,11,
                JCIdent.class ,13);
    }

    /** Test scanning \nonnullelements expression */
    public void testNonnullelements() {
        helpExpr(" \\nonnullelements(a+b)",
                JCMethodInvocation.class, 17,
                JmlFunction.class, 1,
                JCBinary.class, 19,
                JCIdent.class ,18,
                JCIdent.class ,20);
    }

    /** Test scanning \typeof expression */
    public void testTypeof() {
        helpExpr(" \\typeof(a+b)",
                JCMethodInvocation.class, 8,
                JmlFunction.class, 1,
                JCBinary.class, 10,
                JCIdent.class ,9,
                JCIdent.class ,11);
    }

    /** Test scanning \max(\lockset) expression */
    public void testMaxLockset() {
        helpExpr(" \\max(\\lockset)",
                JCMethodInvocation.class, 5,
                JmlFunction.class, 1,
                JmlSingleton.class, 6);
    }

    /** Test scanning \max(\lockset) expression */
    public void testMaxLocksetError2() {
        helpExprErrors(" \\max","/TEST.java:1: reached end of file while parsing");
    }

    /** Test precedence of <: operator */
    public void testCompare() {
        helpExpr(" a == b <= c",
                JCBinary.class, 8, // FIXME - Bug in Parser, should be 3
                JCIdent.class, 1,
                JCBinary.class, 8,
                JCIdent.class ,6,
                JCIdent.class ,11);
    }

    /** Test precedence of <: operator */
    public void testCompare2() {
        helpExpr(" a <= b == c",
                JCBinary.class, 8,
                JCBinary.class, 3,
                JCIdent.class, 1,
                JCIdent.class ,6,
                JCIdent.class ,11);
    }
    /** Test precedence of <: operator */
    public void testSubTypeof() {
        helpExpr(" a == b <: c",
                JCBinary.class, 8, // FIXME - Bug in Parser, should be 3
                JCIdent.class, 1,
                JmlBinary.class, 8,
                JCIdent.class ,6,
                JCIdent.class ,11);
    }

    /** Test precedence of <: operator */
    public void testSubTypeof2() {
        helpExpr(" a <: b == c",
                JCBinary.class, 8,
                JmlBinary.class, 3,
                JCIdent.class, 1,
                JCIdent.class ,6,
                JCIdent.class ,11);
    }
    
    /** Test precedence of <: operator */
    public void testSubTypeof3() {
        helpExpr(" a <: b << c",
                JmlBinary.class, 8, // FIXME - Bug in parser, should be 3
                JCIdent.class, 1,
                JCBinary.class, 8,
                JCIdent.class ,6,
                JCIdent.class ,11);
    }
    
    /** Test precedence of <: operator */
    public void testSubTypeof4() {
        helpExpr(" a << b <: c",
                JmlBinary.class, 8,
                JCBinary.class, 3,
                JCIdent.class, 1,
                JCIdent.class ,6,
                JCIdent.class ,11);
    }
    
    public void testQuantifier() {
        helpExpr(" \\exists  int i; 0 <= i; i < 0  ",
                JmlQuantifiedExpr.class,1,
                JCPrimitiveTypeTree.class, 10,
                JCBinary.class, 19,
                JCLiteral.class ,17,
                JCIdent.class ,22,
                JCBinary.class ,27,
                JCIdent.class ,25,
                JCLiteral.class ,29);
    }

    public void testQuantifier2() {
        helpExpr("(\\forall  int i; 0 <= i; i < 0 ) ",
                JCParens.class, 0,
                JmlQuantifiedExpr.class,1,
                JCPrimitiveTypeTree.class, 10,
                JCBinary.class, 19,
                JCLiteral.class ,17,
                JCIdent.class ,22,
                JCBinary.class ,27,
                JCIdent.class ,25,
                JCLiteral.class ,29);
    }

    public void testQuantifier3() {
        helpExpr("(\\sum     int i; 0 <= i; i + 1 ) ",
                JCParens.class, 0,
                JmlQuantifiedExpr.class,1,
                JCPrimitiveTypeTree.class, 10,
                JCBinary.class, 19,
                JCLiteral.class ,17,
                JCIdent.class ,22,
                JCBinary.class ,27,
                JCIdent.class ,25,
                JCLiteral.class ,29);
    }

    public void testQuantifier4() {
        helpExpr("(\\product int i; ; i + 1 ) ",
                JCParens.class, 0,
                JmlQuantifiedExpr.class,1,
                JCPrimitiveTypeTree.class, 10,
                JCBinary.class ,21,
                JCIdent.class ,19,
                JCLiteral.class ,23);
    }

    public void testQuantifier5() {
        helpExpr("(\\min     int i;   i + 1 ) ",
                JCParens.class, 0,
                JmlQuantifiedExpr.class,1,
                JCPrimitiveTypeTree.class, 10,
                JCBinary.class ,21,
                JCIdent.class ,19,
                JCLiteral.class ,23);
    }

    public void testQuantifier6() {
        helpExpr("(\\max     int i;   i + 1 ) ",
                JCParens.class, 0,
                JmlQuantifiedExpr.class,1,
                JCPrimitiveTypeTree.class, 10,
                JCBinary.class ,21,
                JCIdent.class ,19,
                JCLiteral.class ,23);
    }

//    public void testMisc() {
//        print = true;
//        helpExpr("(\\result==j) ==> \\typeof(o) <: \\type(oo) ",
//                JCParens.class, 0,
//                JmlQuantifiedExpr.class,1,
//                JCPrimitiveTypeTree.class, 10,
//                JCBinary.class ,21,
//                JCIdent.class ,19,
//                JCLiteral.class ,23);
//    }




}

