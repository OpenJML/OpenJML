package tests;
import java.util.List;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import junit.framework.AssertionFailedError;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.tools.javac.parser.JmlFactory;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Parser;
import com.sun.tools.javac.parser.Token;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCConditional;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.Log;

/** These test the AST structure produced by parsing various expressions -
 * checking the node type and position.
 * @author David Cok
 */
public class expressions extends ParseBase {

    protected void setUp() throws Exception {
        //noCollectDiagnostics = true;
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
            JmlParser p = ((JmlFactory)fac).newParser(s,false,true,true,true);
            if (jml) {
                p.getScanner().setJml(jml);
            }
            JCTree.JCExpression e = p.parseExpression();
            List<JCTree> out = ParseTreeScanner.walk(e);
            int i = 0;
            int k = 0;
            if (print) {
                for (JCTree t: out) {
                    System.out.println(t.getClass() + " " + t.getPreferredPosition());
                }
            }
            if (print || collector.getDiagnostics().size() != 0)
                printErrors();
            if (collector.getDiagnostics().size() != 0) {
                fail("Saw unexpected errors");
            }
//            if (out.size()*2 != list.length) {
//                assertEquals("Incorrect number of nodes listed",list.length/2,out.size());
//            }
            Object p1, p2, p3;
            for (JCTree t: out) {
                assertEquals("Class not matched at token " + k, list[i++], t.getClass());
                p1 = list[i++];
                p2 = (i < list.length && list[i] instanceof Integer) ? list[i++] : null;
                p3 = (i < list.length && list[i] instanceof Integer) ? list[i++] : null;
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
            if ( i != list.length) fail("Incorrect number of nodes listed");

            if (p.getScanner().token() != Token.EOF) fail("Not at end of input");
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    public void helpExprErrors(String s, Object... list) {
        try {
            Log.instance(context).useSource(new TestJavaFileObject(s));
            Parser p = ((JmlFactory)fac).newParser(s,false,true,true,jml);
            //JmlScanner sc = ((JmlParser)p).getScanner();
            //if (jml) sc.setJml(jml);
            p.parseExpression();
            int i = 0;
            if (print || collector.getDiagnostics().size() != list.length) printErrors();
            assertEquals("Saw wrong number of errors ",list.length,collector.getDiagnostics().size());
            for (Diagnostic<? extends JavaFileObject> dd: collector.getDiagnostics()) {
                assertEquals("Error message " + i,list[i++],noSource((JCDiagnostic)dd));
            }
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }
    
    String noSource(JCDiagnostic dd) {
        return dd.noSource();
        //return dd.getMessage(Locale.getDefault());
        //defaultFormatter.format(this,Locale.getDefault(),"%f:%l:%_%t%m");
    }


    /** Test scanning something very simple */
    public void testSomeJava() {
        jml = false;
        helpExpr("a",
                JCIdent.class ,0,0,1);
        helpExpr("aaa",
                JCIdent.class ,0,0,3);
    }

    /** Test scanning Java binary expression to check node positions */
    public void testBinary() {
        jml = false;
        helpExpr("aa+bbb",
                JCBinary.class, 0,2,6,
                JCIdent.class ,0,0,2,
                JCIdent.class ,3,3,6);
    }

    /** Test scanning Java binary expression to check node positions */
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
    public void testJMLBinary1() {
        helpExpr("a <==> b",
                JmlBinary.class, 2,
                JCIdent.class ,0,
                JCIdent.class ,7);
    }

    /** Test scanning JML inequivalence expression */
    public void testJMLBinary2() {
        helpExpr("a <=!=>b",
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8);
    }

    /** Test scanning JML implies expression */
    public void testJMLBinary3() {
        helpExpr("a ==>  b",
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8);
    }

    /** Test scanning JML reverse implies expression */
    public void testJMLBinary4() {
        helpExpr("a <==  b",
                JmlBinary.class, 0,2,8,
                JCIdent.class ,0,0,1,
                JCIdent.class ,7,7,8);
    }

    /** Test JML left association for <==> */
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

    /** Test precedence between lock and other operators */
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
    public void testResult() {
        helpExpr(" \\result + \\result",
                JCBinary.class, 9,
                JmlSingleton.class ,1,
                JmlSingleton.class ,11);
    }

    /** Test scanning \old expression */
    public void testOld() {
        helpExpr(" \\old(a+b)",
                JmlMethodInvocation.class, 5,
                JCBinary.class, 7,
                JCIdent.class ,6,
                JCIdent.class ,8);
    }

    /** Test scanning \elemtype expression */
    public void testElemtype() {
        helpExpr(" \\elemtype(a+b)",
                JmlMethodInvocation.class, 10,
                JCBinary.class, 12,
                JCIdent.class ,11,
                JCIdent.class ,13);
    }

    /** Test scanning \nonnullelements expression */
    public void testNonnullelements() {
        helpExpr(" \\nonnullelements(a+b)",
                JmlMethodInvocation.class, 17,
                JCBinary.class, 19,
                JCIdent.class ,18,
                JCIdent.class ,20);
    }

    /** Test scanning \typeof expression */
    public void testTypeofA() {
        helpExpr(" \\typeof(a+b)",
                JmlMethodInvocation.class, 8,
                JCBinary.class, 10,
                JCIdent.class ,9,
                JCIdent.class ,11);
    }

    /** Test scanning \max(\lockset) expression */
    public void testMaxLockset() {
        helpExpr(" \\max(\\lockset)",
                JmlMethodInvocation.class, 5,
                JmlSingleton.class, 6);
    }

    /** Test scanning \max(\lockset) expression */
    public void testMaxLocksetError2() {
        helpExprErrors(" \\max","/TEST.java:1: reached end of file while parsing");
    }

    /** Test precedence of <= operator */
    public void testCompare() {
        helpExpr(" a == b <= c",
                JCBinary.class, 1,3,12,
                  JCIdent.class, 1,1,2,
                  JCBinary.class, 6,8,12,
                    JCIdent.class ,6,6,7,
                    JCIdent.class ,11,11,12);
    }

    /** Test precedence of <= operator */
    public void testCompare2() {
        helpExpr(" a <= b == c",
                JCBinary.class, 1,8,12,
                  JCBinary.class, 1,3,7,
                    JCIdent.class, 1,1,2,
                    JCIdent.class ,6,6,7,
                  JCIdent.class ,11,11,12);
    }
    /** Test precedence of <: operator */
    public void testSubTypeof() {
        helpExpr(" a == b <: c",
                JCBinary.class, 1,3,12,
                  JCIdent.class, 1,1,2,
                  JmlBinary.class, 6,8,12,
                    JCIdent.class ,6,6,7,
                    JCIdent.class ,11,11,12);
    }

    /** Test precedence of <: operator */
    public void testSubTypeof2() {
        helpExpr(" a <: b == c",
                JCBinary.class, 1,8,12,
                JmlBinary.class, 1,3,7,
                  JCIdent.class, 1,1,2,
                  JCIdent.class ,6,6,7,
                JCIdent.class ,11,11,12);
    }
    
    /** Test precedence of <: operator */
    public void testSubTypeof3() {
        helpExpr(" a <: b << c",
                JmlBinary.class, 3, // FIXME - Bug in parser, should be 3
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
                JmlVariableDecl.class,14,
                JCModifiers.class,10,
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
                JmlVariableDecl.class,14,
                JCModifiers.class,10,
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
                JmlVariableDecl.class,14,
                JCModifiers.class,10,
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
                JmlVariableDecl.class,14,
                JCModifiers.class,10,
                JCPrimitiveTypeTree.class, 10,
                JCBinary.class ,21,
                JCIdent.class ,19,
                JCLiteral.class ,23);
    }

    public void testQuantifier5() {
        helpExpr("(\\min     int i;   i + 1 ) ",
                JCParens.class, 0,
                JmlQuantifiedExpr.class,1,
                JmlVariableDecl.class,14,
                JCModifiers.class,10,
                JCPrimitiveTypeTree.class, 10,
                JCBinary.class ,21,
                JCIdent.class ,19,
                JCLiteral.class ,23);
    }

    public void testQuantifier6() {
        helpExpr("(\\max     int i;   i + 1 ) ",
                JCParens.class, 0,
                JmlQuantifiedExpr.class,1,
                JmlVariableDecl.class,14,
                JCModifiers.class,10,
                JCPrimitiveTypeTree.class, 10,
                JCBinary.class ,21,
                JCIdent.class ,19,
                JCLiteral.class ,23);
    }

    // Just a framework used for debugging and new tests
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

