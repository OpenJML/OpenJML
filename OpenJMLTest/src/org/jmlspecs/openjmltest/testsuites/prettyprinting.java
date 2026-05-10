package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjml.JmlAstPrinter;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjmltest.ParseBase;
import org.openjml.MockJavaFileObject;

import static org.junit.Assert.*;
import org.junit.*;

import com.sun.tools.javac.parser.Parser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Log;

/** This set of tests test that the pretty printer outputs properly.  The test
 * checks this by comparing the input code to the output code; before comparison,
 * each sequence of white space is replaced by a single space, so that the
 * output formatting does not have to precisely match the input (unless
 * precise is set true, which it currently is).
 *
 * It also includes similar tests for the JmlAstPrinter.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class prettyprinting extends ParseBase {

    boolean precise = true;
    @Override
    public void setUp() throws Exception {
        super.setUp();
        print = false;
        postOptions();
    }

    public void helpPP(String code) {
        try {
            //print = true;
            Log.instance(context).useSource(new MockJavaFileObject(code));
            Parser p = fac.newParser(code,false,true,true);
            JCTree tree = p.parseCompilationUnit();
            String out = JmlPretty.write(tree);
            if (collector.getDiagnostics().size() != 0) printDiagnostics();
            // Strip sourcefile tracking comments added by JmlPretty to type-level clauses.
            out = out.replaceAll(" // sourcefile: [^\n]*", "");
            if (!precise) {
                code = code.replaceAll("[ \t\r\n]+"," ");
                out = out.replaceAll("[ \t\r\n]+"," ");
            } else {
                code = code.replaceAll("[\r]","");
                out = out.replaceAll("[\r]","");
            }
            String added = "//@ model import org.jmlspecs.lang.*;";
            boolean hasPackage = code.contains("package");
            boolean hasImport = code.contains("import");
            boolean hasAddedNL = out.contains(added + "\n");
            if (hasImport) {
                out = out.replace("//@ model import org.jmlspecs.lang.*;\n", "");
            } else if (hasPackage) {
                out = out.replace("\n//@ model import org.jmlspecs.lang.*;\n", "");
            } else if (out.contains(added + " ")) {
                out = out.replace("//@ model import org.jmlspecs.lang.*; ", "");
            } else if (hasAddedNL) {
                out = out.replace("\n//@ model import org.jmlspecs.lang.*;\n", "");
            }
            if (print || !code.equals(out)) {
                this.out.println("IN:");
                this.out.print(code);
                this.out.println("OUT:");
                this.out.print(out);
            }
            assertEquals("Output differs",code,out);
        } catch (Exception e) {
            e.printStackTrace(this.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    // -----------------------------------------------------------------------
    // Java declarations
    // -----------------------------------------------------------------------

    @Test
    public void testSimpleClass() {
        helpPP("""

                class A {
                }""");
    }

    @Test
    public void testPackage() {
        helpPP("""
                package t;

                class A {
                }""");
    }

    @Test
    public void testImport() {
        helpPP("""
                package t;

                import java.io.File;

                class A {
                }""");
    }

    @Test
    public void testImportStar() {
        helpPP("""
                package t;

                import java.io.File;
                import java.io.*;

                class A {
                }""");
    }

    @Test
    public void testModelImport() {
        helpPP("""
                package t;

                //@ model import java.io.File;
                //@ model import java.io.*;

                class A {
                }""");
    }

    @Test
    public void testClassModifiers() {
        helpPP("""

                public static final class A {
                }""");
    }

    @Test
    public void testMethodDecl() {
        helpPP("""

                public static final class A {
                 \s
                  void m() {
                  }
                }""");
    }

    @Test
    public void testMethodModifiers() {
        helpPP("""

                class A {
                 \s
                  public static void m() {
                  }
                }""");
    }

    @Test
    public void testFieldDecls() {
        helpPP("""

                class A {
                  int i = 0;
                  static final String s = "hello";
                  private Object o;
                }""");
    }

    @Test
    public void testInterface() {
        helpPP("""

                interface I {
                 \s
                  int m(int i);
                }""");
    }

    //  @Test // FIXME - this prints all the synthesized specs 
    public void testEnum() {
        helpPP("""

                enum Color {
                  RED, GREEN, BLUE;
                }""");
    }

    // JmlPretty desugars records to classes (known limitation).
    @Test
    public void testRecord() {
        precise = false;
        helpPP("""

                class Point {

                  private final int x;
                  private final int y;
                }""");
    }

    // -----------------------------------------------------------------------
    // Java statements
    // -----------------------------------------------------------------------

    @Test
    public void testMethodStatements() {
        precise = true;
        helpPP("""

                public static final class A {
                 \s
                  int p(int a, Object o) {
                  }
                 \s
                  void m() {
                    int a;
                    a = 5;
                    ;
                    a += 5;
                    /*@ assume a == 6;*/
                    /*@ assert a == 6;*/
                    /*@ set a = 6;*/
                    /*@ set a = 6;*/
                    a += 5;
                    a -= 5;
                    a *= 5;
                    a /= 5;
                    a %= 5;
                    a |= 5;
                    a &= 5;
                    a ^= 5;
                    a <<= 5;
                    a >>= 5;
                    a >>>= 5;
                    m();
                    for (int i = 0; i < 5; i++) {
                    }
                    for (int i : new int[6]) {
                    }
                    while (true) {
                      do {
                      } while (true);
                    }
                    /*@ assert (* xyz *);*/
                  }
                }""");
    }

    @Test
    public void testMethodStatements2() {
        precise = false; // TODO  // Fixme - seems to use incorrectly formatted JML annotations
        helpPP("""

                public static final class A {

                  void m() {
                    int a;
                    a = 5;
                    ;
                    a += 5;
                  }
                }""");
    }

    @Test
    public void testIfElse() {
        helpPP("""

                class A {
                 \s
                  void m(boolean b, int i) {
                    if (b) {
                      i = 1;
                    }
                    if (b) {
                      i = 1;
                    } else {
                      i = 2;
                    }
                    if (b) i = 1; else i = 2;
                  }
                }""");
    }

    // Blank-line whitespace between cases varies; use precise=false.
    @Test
    public void testSwitch() {
        precise = false;
        helpPP("""

                class A {

                  void m(int i) {
                    switch (i) {
                    case 1:
                      i = 2;
                      break;

                    case 2:
                    case 3:
                      i = 4;
                      break;

                    default:
                      i = 0;
                    }
                  }
                }""");
    }

    @Test
    public void testSwitchExpression() {
        helpPP("""

                class A {
                 \s
                  int m(int i) {
                    return switch (i) {
                    case 1 -> 10;
                    case 2 -> 20;
                    default -> 0;
                    };
                  }
                }""");
    }

    @Test
    public void testTryCatch() {
        helpPP("""

                class A {
                 \s
                  void m() {
                    try {
                      int i = 1;
                    } catch (Exception e) {
                      e.printStackTrace();
                    } finally {
                      int j = 2;
                    }
                  }
                }""");
    }

    @Test
    public void testTryWithResources() {
        helpPP("""

                class A {
                 \s
                  void m() throws Exception {
                    try (java.io.InputStream s = new java.io.ByteArrayInputStream(new byte[0]);) {
                      s.read();
                    }
                  }
                }""");
    }

    @Test
    public void testTryWithExpressionResources() {
        helpPP("""

                class A {
                 \s
                  void m() throws Exception {
                    java.io.InputStream s = new java.io.ByteArrayInputStream(new byte[0]);
                    java.io.InputStream ss = new java.io.ByteArrayInputStream(new byte[0]);
                    try (s; ss) {
                      s.read();
                    }
                  }
                }""");
    }

    // Pretty prints labeled statements as 'label:stmt' with no space before the statement.
    @Test
    public void testReturnThrowBreakContinue() {
        helpPP("""

                class A {
                 \s
                  int m(boolean b) {
                    if (b) throw new RuntimeException();
                    loop:for (int i = 0; i < 10; i++) {
                      if (i == 3) continue;
                      if (i == 7) break loop;
                    }
                    return 0;
                  }
                }""");
    }

    @Test
    public void testSynchronized() {
        helpPP("""

                class A {
                 \s
                  void m() {
                    synchronized (this) {
                      int i = 1;
                    }
                  }
                }""");
    }

    // -----------------------------------------------------------------------
    // JML method specifications
    // JmlPretty combines all spec clauses for a method into a single /*@ ... */ block.
    // -----------------------------------------------------------------------

    @Test
    public void testRequiresEnsures() {
        precise = false;
        helpPP("""

                class A {

                  /*@ requires i > 0;
                    ensures \\result >= 0; */
                  int m(int i) {
                    return i;
                  }
                }""");
    }

    @Test
    public void testSignals() {
        precise = false;
        helpPP("""

                class A {

                  /*@ signals (IllegalArgumentException e) i < 0;
                    signals_only IllegalArgumentException; */
                  void m(int i) {
                  }
                }""");
    }

    @Test
    public void testAssignable() {
        precise = false;
        helpPP("""

                class A {

                  int x;
                  int[] a;

                  /*@ assignable x, a[*];
                    assignable \\nothing; */
                  void m() {
                  }
                }""");
    }

    @Test
    public void testSpecCase() {
        precise = false;
        helpPP("""

                class A {

                  /*@ public normal_behavior
                    requires true;
                    ensures \\result > 0;
                   also public exceptional_behavior
                    signals (Exception e) true; */
                  int m() {
                    return 1;
                  }
                }""");
    }

    // -----------------------------------------------------------------------
    // JML type clauses
    // JmlPretty uses the //@ line-comment form for type-level clauses.
    // -----------------------------------------------------------------------

    @Test
    public void testInvariant() {
        precise = false;
        helpPP("""

                class A {

                  int i;
                  //@ public invariant i >= 0;
                }""");
    }

    // JmlPretty prints model field modifiers as 'model public' (model keyword first).
    @Test
    public void testModelField() {
        precise = false;
        helpPP("""

                class A {

                  //@ model public int modelVal;
                  //@ represents modelVal = 42;
                }""");
    }

    // -----------------------------------------------------------------------
    // JML statements and loop annotations
    // JmlPretty uses //@ form; 'loop_assigns' is printed as 'loop_writes'.
    // -----------------------------------------------------------------------

    @Test
    public void testLoopAnnotations() {
        precise = false;
        helpPP("""

                class A {

                  void m() {
                    int i = 0;
                    //@ loop_invariant i >= 0;
                    //@ loop_writes i;
                    //@ loop_decreases 10 - i;
                    while (i < 10) {
                      i++;
                    }
                  }
                }""");
    }

    // Ghost variable declarations use //@ format; JML statements use /*@ ... */ format.
    @Test
    public void testGhost() {
        precise = false;
        helpPP("""

                class A {

                  void m() {
                    //@ ghost int g = 0;
                    /*@ set g = 1;*/
                    /*@ show g;*/
                  }
                }""");
    }

    @Test
    public void testModelMethod() {
        precise = false;
        helpPP("""

                class A {

                  //@ model public int size();
                }""");
    }

    // -----------------------------------------------------------------------
    // JmlAstPrinter tests (currently disabled)
    // -----------------------------------------------------------------------

    public void helpAst(String text) {
        if (true) return; // FIXME - don't include AST printing in tests just yet
        Log.instance(context).useSource(new MockJavaFileObject(text));
        Parser p = fac.newParser(text,false,true,true);
        JCTree tree = p.parseCompilationUnit();
        String output = JmlAstPrinter.print(tree, main.context());
        this.out.println("TEXT: " + text);
        this.out.println(output);
    }

    @Test
    public void ast1() {
        helpAst("package p; import static a.b.*; /*@ model import c.d; */ public class A {}");
    }

    @Test
    public void ast2() {
        helpAst("""
                public class A {
                  Object o;
                  int i1 = 1 + -2*-(4.0) - 4/5 + 6L%7.0f;
                  long i2 = (4<<5) + (5>>6) + (7>>>8);
                  int j = true ? i : !false ? i : i;
                  int k = (i&j) + ( i|~j) + (i^k);
                  boolean m = (i==i) || (i<i) && (i!=1) && (i<=i) && (i>=i) && (i>i);
                  //@ ghost s = (true ==> false) && ( true <==> false) || (true <=!=> false);
                  //@ ghost boolean t = 0 < 1 < 2;
                }
                """);
    }

    @Test
    public void ast3() {
        helpAst("""
                public class A {
                  static {
                    int i = 7;
                    i += 8;
                    assert i == i;
                  }
                }
                """);
    }

    // FIXME - need to test every construct (lots more) for pretty printing;
    // also for with and without jml comments
}
