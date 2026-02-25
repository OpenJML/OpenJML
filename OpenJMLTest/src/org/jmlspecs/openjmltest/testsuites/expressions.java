package org.jmlspecs.openjmltest.testsuites;
import java.util.List;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjmltest.IgnoreFalseAssumptions;
import org.jmlspecs.openjmltest.ParseBase;
import org.junit.*;
import org.openjml.MockJavaFileObject;

import com.sun.tools.javac.parser.JmlFactory;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Parser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.Log;

import static org.junit.Assert.*;

// FIXME - verify that the output that occurs is desired

/** These test the AST structure produced by parsing various expressions -
 * checking the node type and position.
 * @author David Cok
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@org.junit.runner.RunWith(org.jmlspecs.openjmltest.IgnoreFalseAssumptions.class)
public class expressions extends ParseBase {
    
    public boolean skip = false;
    public boolean failharness = false;
    
    // FIXME - capture output and check it -- can we do so thread safely?

    @Override
    public void setUp() throws Exception {
        //noCollectDiagnostics = true;
        super.setUp();
        jml = true;
        print = false;
        skip = false;
        failharness = false;
        postOptions();
    }
    
    public void helpFailure(String failureMessage, String s, Object ... list) {
        if (skip) return;
        boolean failed = false;
        try {
            helpExpr(s,list);
        } catch (AssertionError a) {
            failed = true;
            assertEquals("Failure report wrong",failureMessage,a.getMessage());
        }
        assertTrue("Test harness failed to report an error", failed);
    }

    public void helpExpr(String s, Object... list) {
        if (skip) return;
        List<JCTree> nodes = null;
        JmlParser p = null;
        try {
            if (failharness) throw new IllegalArgumentException();
            Log.instance(context).useSource(new MockJavaFileObject(s));
            p = ((JmlFactory)fac).newParser(s,false,jml);
            JCTree.JCExpression e = p.parseExpression();
            nodes = ParseTreeScanner.walk(e);
            int i = 0;
            int k = 0;
            if (print) {
                for (JCTree t: nodes) {
                    this.out.println(t.getClass() 
                            + " " + t.getStartPosition() 
                            + " " + t.getPreferredPosition() 
                            + " " + p.getEndPos(t));
                }
            }
            printDiagnostics(); // There should be no errors
            assertTrue("Saw unexpected errors", collector.getDiagnostics().size() == 0);

            Object p1, p2, p3;
            for (JCTree t: nodes) {
                assertEquals("Class not matched at token " + k, list[i++], t.getClass());
                p1 = list[i++];
                p2 = (i < list.length && list[i] instanceof Integer) ? list[i++] : null;
                p3 = (i < list.length && list[i] instanceof Integer) ? list[i++] : null;
                // FIXME - need better way to obtain positions
                if (p3 != null) {
                    assertEquals("Start position for token " + k, p1, t.getStartPosition());
                    assertEquals("Preferred position for token " + k, p2, t.getPreferredPosition());
                    assertEquals("End position for token " + k, p3, p.getEndPos(t));
                } else if (p2 != null) {
                    assertEquals("Start position for token " + k, p1, t.getStartPosition());
                    assertEquals("End position for token " + k, p2, p.getEndPos(t));
                } else {
                    assertEquals("Preferred position for token " + k, p1, t.getPreferredPosition());
                }
                ++k;
            }
            assertTrue("Incorrect number of nodes listed", i == list.length);
            assertTrue("Not at end of input", p.getScanner().token().kind == TokenKind.EOF);
        } catch (AssertionError e) {
            if (nodes != null) for (JCTree t: nodes) {
                this.out.println(t.getClass() 
                        + " " + t.getStartPosition() 
                        + " " + t.getPreferredPosition() 
                        + " " + p.getEndPos(t));
            }
            throw e;
        } catch (Exception e) { // An exception is thrown only if there is an internal bug
            e.printStackTrace(this.out);
            fail("Exception thrown while processing test: " + e); // NOCOV: Always throws exception -- won't show as covered
        }
    }

    public void helpExprErrors(String s, Object... list) {
        if (skip) return;
        try {
            if (failharness) throw new IllegalArgumentException();
            Log.instance(context).useSource(new MockJavaFileObject(s));
            Parser p = ((JmlFactory)fac).newParser(s,false,true,true,false,jml);
            p.parseExpression();
            int i = 0;
            if (print || collector.getDiagnostics().size() != list.length) printDiagnostics();
            assertEquals("Saw wrong number of errors ",list.length,collector.getDiagnostics().size());
            for (Diagnostic<? extends JavaFileObject> dd: collector.getDiagnostics()) {
                assertEquals("Error message " + i,list[i++],noSource((JCDiagnostic)dd));
            }
        } catch (Exception e) { // An exception is thrown only if there is an internal bug
            e.printStackTrace(this.out);
            fail("Exception thrown while processing test: " + e); // NOCOV: Always throws exception -- won't show as covered
        }
    }
    
//    String noSource(JCDiagnostic dd) {  // FIXME - delete in favor of JmlTestSuite.noSource?
//        return dd.getMessage(java.util.Locale.getDefault());
//    }
    
    /////////////////////////////////////////////////////////
    

    /** Test that fails */
    @Test
    public void testFailure1() {
        jml = false;
        helpFailure("Incorrect number of nodes listed", "a",
                JCIdent.class, 0, 1,
                JCIdent.class, 0, 1);
    }
    
    /** Test that fails */
    @Test
    public void testFailure3() {
        try {
            jml = false; // Intentionally prints output
            helpExpr("#",
                    JCIdent.class, 0, 1,
                    JCIdent.class, 0, 1);
        } catch (AssertionError ex) {
            assertEquals("Saw unexpected errors", ex.getMessage());
        }
    }

    /** Test that fails */
    @Test
    public void testFailure4() {
        try {
            jml = false;
            helpExpr("a a",
                    JCIdent.class, 0, 1);
        } catch (AssertionError ex) {
            assertEquals("Not at end of input", ex.getMessage());
        }
    }
    
    @Test
    public void testFailure5() {
        try { 
            helpExprErrors(" \\max","reached end of file while parsing","ZZZ");
        } catch (AssertionError ex) {
            assertEquals("Saw wrong number of errors  expected:<2> but was:<1>", ex.getMessage());
        }
    }

    @Test
    public void testFailure6() {
        print = true; // Intentionally prints output
        helpExprErrors(" \\max","/TEST.java:1: error: reached end of file while parsing");
    }

    /** Test that fails */
    @Test
    public void testFailure0() {
        try { 
            jml = false;
            helpFailure("", "a", JCIdent.class, 0, 1);
        } catch (AssertionError ex) {
            assertEquals("Test harness failed to report an error", ex.getMessage());
        }
    }

    /** Test that fails */
    @Test
    public void testFailure2() {
        try { 
            jml = false;
            helpFailure("ZZZ", "a",
                                JCIdent.class, 0, 1,
                                JCIdent.class, 0, 1);
        } catch (AssertionError ex) {
            assertEquals("Failure report wrong expected:<[ZZZ]> but was:<[Incorrect number of nodes listed]>",
                    ex.getMessage());
        }
    }
    
    // These tests are simply to improve coverage in failure paths of the helper methods
    @Test
    public void testFailureNone() {
        skip = true;
        testFailure0();
        testFailure2();
        testFailure3();
        testFailure4();
        jml = true;
        testFailure5();
    }

    // These tests are simply to improve coverage in failure paths of the helper methods
    @Test
    public void testFailureNone1() {
        skip = false;
        for (int i = 0; i<2; i++) {
            failharness = i == 0; // Intentional failure and stack output
            skip = i != 0;
            try {
                helpExpr("");
            } catch (AssertionError e) {
                assertEquals("Exception thrown while processing test: java.lang.IllegalArgumentException", e.getMessage());
            }
        }
    }

    // These tests are simply to improve coverage in failure paths of the helper methods
    @Test
    public void testFailureNone2() {
        for (int i = 0; i<2; i++) {
            failharness = i == 0; // Intentional failure and stack output
            skip = i != 0;
            try {
                helpExprErrors("");
            } catch (AssertionError e) {
                assertEquals("Exception thrown while processing test: java.lang.IllegalArgumentException", e.getMessage());
            }
        }
    }

    ///////////////////////////////////////////////////////////////////
    
    // Each bit of source text (in this series of tests, each must be a
    // JML expression) is parsed into a tree of nodes. The expected data
    // for each expression is a preorder (node, left subtree, right subtree)
    // of the tree, giving the node class, the start position, the preferred
    // position and the end position for each node. The positions are 
    // character counts beginning with 0; the end position is one beyond
    // the end of the substring.
    
    @Test
    public void testBug2() {
    	helpExpr("equals(\\result.multiply(val).add(remainder(val)))"
    			,JCMethodInvocation.class, 0,6,49
    			,JCIdent.class, 0,0,6
    			,JCMethodInvocation.class, 7,32,48
    			,JCFieldAccess.class, 7,28,32
    			,JCMethodInvocation.class, 7,23,28
    			,JCFieldAccess.class, 7,14,23
    			,JmlSingleton.class, 7,7,14
    			,JCIdent.class, 24,24,27
    			,JCMethodInvocation.class, 33,42,47
    			,JCIdent.class, 33,33,42
    			,JCIdent.class, 43,43,46
         );
    }

    @Test
    public void testBug() {
    	helpExpr("equals(\\result[0].equals(divide(val)))"
    			,JCMethodInvocation.class, 0,6,38
    			,JCIdent.class, 0,0,6
    			,JCMethodInvocation.class, 7,24,37
    			,JCFieldAccess.class, 7,17,24
    			,JCArrayAccess.class, 7,14,17
    			,JmlSingleton.class, 7,7,14
    			,JCLiteral.class, 15,15,16
    			,JCMethodInvocation.class, 25,31,36
    			,JCIdent.class, 25,25,31
    			,JCIdent.class, 32,32,35
         );
    }

    /** Test scanning something very simple */
    @Test
    public void testSomeJava() {
        jml = false;
        helpExpr("a",
                JCIdent.class ,0,0,1);
        helpExpr("aaa",
                JCIdent.class ,0,0,3);
    }

    /** Test scanning something very simple */
    @Test
    public void testSomeJavaZ() {
        jml = false;
        helpExpr("a",
                JCIdent.class ,0,1); // Intentionally just two positions, to cover that case in the test handler
        helpExpr("aaa",
                JCIdent.class ,0,3);
    }

    /** Test scanning something very simple */
    @Test
    public void testSomeJavaP() {
        jml = false;
        print = true; // Intentionally prints output
        helpExpr("a",
                JCIdent.class ,0,0,1);
    }
    /** Test scanning Java binary expression to check node positions */
    @Test
    public void testBinary() {
        jml = false;
        helpExpr("aa+bbb",
                JCBinary.class, 0,2,6,
                JCIdent.class ,0,0,2,
                JCIdent.class ,3,3,6);
    }

    /** Test scanning Java binary expression to check node positions */
    @Test
    public void testJCBinary() {
        jml = false;
        helpExpr("a+b*c",
                JCBinary.class, 0,1,5,
                  JCIdent.class ,0,0,1,
                  JCBinary.class, 2,3,5,
                    JCIdent.class ,2,2,3,
                    JCIdent.class ,4,4,5
                );
        helpExpr("a*b+c",
                JCBinary.class, 0,3,5,
                  JCBinary.class, 0,1,3,
                    JCIdent.class ,0,0,1,
                    JCIdent.class ,2,2,3,
                  JCIdent.class ,4,4,5
                );
    }

    /** Test scanning JML equivalence expression */
    @Test
    public void testJMLUnary1() {
        helpExpr(" - (++a) + !b + (a--) + (~a++)",
                JCBinary.class, 1,22,30,
                JCBinary.class, 1,14,21,
                JCBinary.class, 1,9,13,

                JCUnary.class, 1,1,8,
                JCParens.class, 3,3,8,
                JCUnary.class, 4,4,7,
                JCIdent.class ,6,6,7,

                JCUnary.class, 11,11,13,
                JCIdent.class ,12,12,13,
                
                JCParens.class, 16,16,21,
                JCUnary.class, 17,18,20,
                JCIdent.class ,17,17,18,
                
                JCParens.class, 24,24,30,
                JCUnary.class, 25,25,29,
                JCUnary.class, 26,27,29,
                JCIdent.class ,26,26,27
                );
    }

    /** Test scanning JML equivalence expression */
    @Test
    public void testJMLBinary1() {
        helpExpr("a <==> b",
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8);
    }

    /** Test scanning JML inequivalence expression */
    @Test
    public void testJMLBinary2() {
        helpExpr("a <=!=>b",
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8);
    }

    /** Test scanning JML implies expression */
    @Test
    public void testJMLBinary3() {
        helpExpr("a ==>  b",
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8);
    }

    /** Test scanning JML reverse implies expression */
    @Test
    public void testJMLBinary4() {
        helpExpr("a <==  b",
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8);
    }

    /** Test JML left association for <==> */
    @Test
    public void testJMLprecedence() {
        helpExpr("a <==> b <==> c <==> d",
                JmlBinary.class, 0,16,22,
                JmlBinary.class, 0,9,15,
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8,
                JCIdent.class ,14,14,15,
                JCIdent.class ,21,21,22);
    }

    /** Test JML right association for ==> */
    @Test
    public void testJMLprecedence1() {
        helpExpr("a ==>  b ==>  c ==>  d",
                JmlBinary.class, 0,2,22,
                JCIdent.class ,0,0,1,
                JmlBinary.class, 7,9,22, 
                JCIdent.class ,7,7,8,
                JmlBinary.class, 14,16,22, 
                JCIdent.class ,14,14,15,
                JCIdent.class ,21,21,22);
    }

    /** Test JML left association for <== */
    @Test
    public void testJMLprecedence1a() {
        helpExpr("a <==  b <==  c <==  d",
                JmlBinary.class, 0,16,22,
                JmlBinary.class, 0,9,15,
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8,
                JCIdent.class ,14,14,15,
                JCIdent.class ,21,21,22);
    }

    /** Test precedence between equiv and implies operators */
    @Test
    public void testJMLprecedence2() {
        helpExpr("a ==>  b <==> c ==>  d",
                JmlBinary.class, 0,9,22,
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8,
                JmlBinary.class, 14,16,22,
                JCIdent.class ,14,14,15,
                JCIdent.class ,21,21,22);
    }

    /** Test association of equiv operators */
    @Test
    public void testJMLprecedence2a() {
        helpExpr("a <==> b <==> c <==> d",
                JmlBinary.class, 0,16,22,
                JmlBinary.class, 0,9,15,
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8,
                JCIdent.class ,14,14,15,
                JCIdent.class ,21,21,22);
    }

    /** Test precedence between equivalence and Java operators */
    @Test
    public void testJMLprecedence3() {
        helpExpr("a +    b <==> c ||   d",
                JmlBinary.class, 0,9,22,
                JCBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8,
                JCBinary.class, 14,16,22,
                JCIdent.class ,14,14,15,
                JCIdent.class ,21,21,22);
    }

    /** Test precedence between implies and Java operators */
    @Test
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
    @Test
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

    /** Test precedence between lock and other operators */
    @Test
    public void testJMLprecedence6() {
        helpExpr("a << b <# c == d",
                JCBinary.class, 12,
                  JmlBinary.class, 7,
                    JCBinary.class, 2,
                      JCIdent.class ,0,
                      JCIdent.class ,5,
                    JCIdent.class ,10,
                  JCIdent.class ,15
                  );
    }

    /** Test precedence between lock and other operators */
    @Test
    public void testJMLprecedence7() {
        helpExpr("a == b <#=c << d",
                JCBinary.class, 2,
                  JCIdent.class ,0,
                  JmlBinary.class, 7,
                    JCIdent.class ,5,
                    JCBinary.class, 12,
                      JCIdent.class ,10,
                      JCIdent.class ,15
                  );
    }

    /** Test associativity of lock operators */
    @Test
    public void testJMLprecedence8() {
        helpExpr("a <# b <#=c <# d",
                JmlBinary.class, 12,
                JmlBinary.class, 7,
                  JmlBinary.class, 2,
                    JCIdent.class ,0,
                    JCIdent.class ,5,
                  JCIdent.class ,10,
                JCIdent.class ,15
                  );
    }

    /** Test precedence between lock and equivalence */
    @Test
    public void testJMLprecedence9() {
        helpExpr("a <==> b <#=c <==> d",
                JmlBinary.class, 14,
                  JmlBinary.class, 2,
                    JCIdent.class ,0,
                    JmlBinary.class, 9,
                      JCIdent.class ,7,
                      JCIdent.class ,12,
                  JCIdent.class ,19
                  );
    }

    /** Test scanning \result expression */
    @Test
    public void testResult() {
        helpExpr(" \\result + \\result",
                JCBinary.class, 1,9,18,
                JmlSingleton.class ,1,1,8,
                JmlSingleton.class ,11,11,18);
    }

    /** Test scanning \old expression */
    @Test
    public void testOld() {
        helpExpr(" \\old(a+b)",
                JmlMethodInvocation.class, 1,5,10,
                JCBinary.class, 6,7,9,
                JCIdent.class ,6,6,7,
                JCIdent.class ,8,8,9);
    }

    /** Test scanning \elemtype expression */
    @Test
    public void testElemtype() {
        helpExpr(" \\elemtype(a+b)",
                JmlMethodInvocation.class, 1,10,15,
                JCBinary.class, 11,12,14,
                JCIdent.class ,11,11,12,
                JCIdent.class ,13,13,14);
    }

    /** Test scanning \nonnullelements expression */
    @Test
    public void testNonnullelements() {
        helpExpr(" \\nonnullelements(a+b)",
                JmlMethodInvocation.class, 17,
                JCBinary.class, 19,
                JCIdent.class ,18,
                JCIdent.class ,20);
    }

    /** Test scanning \typeof expression */
    @Test
    public void testTypeofA() {
        helpExpr(" \\typeof(a+b)",
                JmlMethodInvocation.class, 8,
                JCBinary.class, 10,
                JCIdent.class ,9,
                JCIdent.class ,11);
    }

    /** Test scanning \max(\lockset) expression */
    @Test
    public void testMaxLockset() {
        helpExpr(" \\max(\\lockset)",
                JmlMethodInvocation.class, 5,
                JmlSingleton.class, 6);
    }

    /** Test scanning \max(\lockset) expression */
    @Test
    public void testMaxLocksetError2() {
        helpExprErrors(" \\max","/TEST.java:1: error: reached end of file while parsing");  // FIXME - a duplicate test?
    }

    /** Test precedence of <= operator */
    @Test
    public void testCompare() {
        helpExpr(" a == b <= c",
                JCBinary.class, 1,3,12,
                  JCIdent.class, 1,1,2,
                  JCBinary.class, 6,8,12,
                    JCIdent.class ,6,6,7,
                    JCIdent.class ,11,11,12);
    }

    /** Test precedence of <= operator */
    @Test
    public void testCompare2() {
        helpExpr(" a <= b == c",
                JCBinary.class, 1,8,12,
                  JCBinary.class, 1,3,7,
                    JCIdent.class, 1,1,2,
                    JCIdent.class ,6,6,7,
                  JCIdent.class ,11,11,12);
    }
    /** Test precedence of <:= operator */
    @Test
    public void testSubTypeof() {
        helpExpr(" a == b <:= c",
                JCBinary.class, 1,3,13,
                  JCIdent.class, 1,1,2,
                  JmlBinary.class, 6,8,13,
                    JCIdent.class ,6,6,7,
                    JCIdent.class ,12,12,13);
    }

    /** Test precedence of <:= operator */
    @Test
    public void testSubTypeof2() {
        helpExpr(" a <:= b == c",
                JCBinary.class, 1,9,13,
                JmlBinary.class, 1,3,8,
                  JCIdent.class, 1,1,2,
                  JCIdent.class, 7,7,8,
                JCIdent.class ,12,12,13);
    }
    
    /** Test precedence of <:= operator */
    @Test
    public void testSubTypeof3() {
        helpExpr(" a <:= b << c",
                JmlBinary.class, 3,
                JCIdent.class, 1,
                JCBinary.class, 9,
                JCIdent.class ,7,
                JCIdent.class ,12);
    }
    
    /** Test precedence of <:= operator */
    @Test
    public void testSubTypeof4() {
        helpExpr(" a << b <:= c",
                JmlBinary.class, 8,
                JCBinary.class, 3,
                JCIdent.class, 1,
                JCIdent.class ,6,
                JCIdent.class ,12);
    }
    
    /** Test precedence of <:= operator */
    @Test
    public void testSubTypeof5() {
        helpExpr(" (a) <:= c",
                JmlBinary.class, 5,
                JCParens.class, 1,
                JCIdent.class, 2,
                JCIdent.class ,9);
    }
    
    /** Test precedence of <:= operator */
    @Test
    public void testSubTypeof6() {
        helpExpr(" a <:= (c)",
                JmlBinary.class, 3,
                JCIdent.class, 1,
                JCParens.class, 7,
                JCIdent.class ,8);
    }
    
    /** Test precedence of <:= operator */
    @Test
    public void testSubTypeof7() {
        helpExpr(" (a) <:= (c)",
                JmlBinary.class, 5,
                JCParens.class, 1,
                JCIdent.class, 2,
                JCParens.class, 9,
                JCIdent.class ,10);
    }
    
    @Test
    public void testQuantifier() {
        helpExpr(" \\exists  int i; 0 <= i; i < 0  ",
                JmlQuantifiedExpr.class,1,1,30,
                JmlVariableDecl.class,10,14,15,
                JmlModifiers.class,10,10,10,
                JCPrimitiveTypeTree.class, 10,10,13,
                JCBinary.class, 17,19,23,
                JCLiteral.class ,17,17,18,
                JCIdent.class ,22,22,23,
                JCBinary.class ,25,27,30,
                JCIdent.class ,25,25,26,
                JCLiteral.class ,29,29,30);
    }

    @Test
    public void testQuantifier2() {
        helpExpr("(\\forall  int i; 0 <= i; i < 0 ) ",
                JCParens.class, 0,0,32,
                JmlQuantifiedExpr.class,1,1,30,
                JmlVariableDecl.class,10,14,15,
                JmlModifiers.class,10,10,10,
                JCPrimitiveTypeTree.class, 10,10,13,
                JCBinary.class, 17,19,23,
                JCLiteral.class ,17,17,18,
                JCIdent.class ,22,22,23,
                JCBinary.class ,25,27,30,
                JCIdent.class ,25,25,26,
                JCLiteral.class ,29,29,30);
    }

    @Test
    public void testQuantifier3() {
        helpExpr("(\\sum     int i; 0 <= i; i + 1 ) ",
                JCParens.class, 0,0,32,
                JmlQuantifiedExpr.class,1,1,30,
                JmlVariableDecl.class,10,14,15,
                JmlModifiers.class,10,10,10,
                JCPrimitiveTypeTree.class, 10,10,13,
                JCBinary.class, 17,19,23,
                JCLiteral.class ,17,17,18,
                JCIdent.class ,22,22,23,
                JCBinary.class ,25,27,30,
                JCIdent.class ,25,25,26,
                JCLiteral.class ,29,29,30);
    }

    @Test
    public void testQuantifier4() {
        helpExpr("(\\product int i; ; i + 1 ) ",
                JCParens.class, 0,0,26,
                JmlQuantifiedExpr.class,1,1,24,
                JmlVariableDecl.class,10,14,15,
                JmlModifiers.class,10,10,10,
                JCPrimitiveTypeTree.class, 10,10,13,
                JCBinary.class ,19,21,24,
                JCIdent.class ,19,19,20,
                JCLiteral.class ,23,23,24);
    }

    @Test
    public void testQuantifier5() {
        helpExpr("(\\min     int i;   i + 1 ) ",
                JCParens.class, 0,0,26,
                JmlQuantifiedExpr.class,1,1,24,
                JmlVariableDecl.class,10,14,15,
                JmlModifiers.class,10,10,10,
                JCPrimitiveTypeTree.class, 10,10,13,
                JCBinary.class ,19,21,24,
                JCIdent.class ,19,19,20,
                JCLiteral.class ,23,23,24);
    }

    @Test
    public void testQuantifier6() {
        helpExpr("(\\max     int i;   i + 1 ) ",
                JCParens.class, 0,0,26,
                JmlQuantifiedExpr.class,1,1,24,
                JmlVariableDecl.class,10,14,15,
                JmlModifiers.class,10,10,10,
                JCPrimitiveTypeTree.class, 10,10,13,
                JCBinary.class ,19,21,24,
                JCIdent.class ,19,19,20,
                JCLiteral.class ,23,23,24);
    }

    @Test
    public void testLet1() {
        helpExpr("(\\let int i=1+2, boolean b = i==i;   i + 1 ) ",
                JCParens.class, 0, 0, 44,
                JmlLetExpr.class, 1, 1, 42,
                JmlVariableDecl.class,6,10, 15,
                JmlModifiers.class, 6,6,6,
                JCPrimitiveTypeTree.class, 6,6,9,
                JCBinary.class, 12,13,15,
                JCLiteral.class, 12,12,13,
                JCLiteral.class, 14,14,15,
                JmlVariableDecl.class, 17,25,33,
                JmlModifiers.class, 17,17,17,
                JCPrimitiveTypeTree.class, 17,17,24,
                JCBinary.class, 29,30,33,
                JCIdent.class, 29,29,30,
                JCIdent.class,32,32,33,
                JCBinary.class, 37,39,42,
                JCIdent.class, 37,37,38,
                JCLiteral.class, 41,41,42
                );
    }

    @Test
    public void testMisc() {
        helpExpr("(\\result==j) ==> \\typeof(o) <:= \\type(oo) "
                ,JmlBinary.class ,0,13,41
                ,JCParens.class, 0,0,12
                ,JCBinary.class ,1,8,11
                ,JmlSingleton.class ,1,1,8
                ,JCIdent.class ,10,10,11
                ,JmlBinary.class ,17,28,41 
                ,JmlMethodInvocation.class, 17,24,27 
                ,JCIdent.class ,25,25,26
                ,JmlMethodInvocation.class, 32,37,41
                ,JCIdent.class ,38,38,40
                );
    }
    
    @Test
    public void testCastResult2() {
    	helpExpr("((Integer)\\result) == 0"
                ,JCBinary.class ,0,19,23
                ,JCParens.class, 0,0,18
                ,JCTypeCast.class ,1,1,17
                ,JCIdent.class ,2,2,9
                ,JmlSingleton.class ,10,10,17 
                ,JCLiteral.class, 22,22,23 
    			);
    }

    @Test
    public void testCastResult() {
    	helpExpr("((x)==>\\result) == 0"
                ,JCBinary.class ,0,16,20
                ,JCParens.class, 0,0,15
                ,JmlBinary.class ,1,4,14
                ,JCParens.class, 1,1,4
                ,JCIdent.class ,2,2,3
                ,JmlSingleton.class ,7,7,14 
                ,JCLiteral.class, 19,19,20 
    			);
    }

// TODO: other expressions, etc.
}
