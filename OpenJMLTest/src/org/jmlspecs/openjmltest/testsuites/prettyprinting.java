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
 * It  also includes similar testsw for the JmlAstPrinter.
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
            //sc = ((JmlParser)p).getScanner();
            JCTree tree = p.parseCompilationUnit();
            String out = JmlPretty.write(tree);
            if (collector.getDiagnostics().size() != 0) printDiagnostics();
            assertEquals("Found parsing errors",0,collector.getDiagnostics().size());
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
                //printTree(ParseTreeScanner.walk(tree));
            }
            assertEquals("Output differs",code,out);
        } catch (Exception e) {
            e.printStackTrace(this.out);
            fail("Exception thrown while processing test: " + e);
        }
    }
    
    @Test
    public void testSimpleClass() {
        helpPP(
                eol +
                "class A {" + eol +
                "}"
        );
    }

    @Test
    public void testPackage() {
        helpPP(
                "package t;" + eol + 
                eol +
                "class A {" + eol +
                "}"
        );
    }

    @Test
    public void testImport() {
        helpPP(
                "package t;" + eol + 
                eol +
                "import java.io.File;" + eol +
                eol +
                "class A {" + eol +
                "}"
        );
    }

    @Test
    public void testImportStar() {
        helpPP(
                "package t;" + eol + eol +
                "import java.io.File;" + eol +
                "import java.io.*;" + eol + eol +
                "class A {" + eol +
                "}"
        );
    }

    @Test
    public void testModelImport() {
        helpPP(
                "package t;" + eol + eol +
                "//@ model import java.io.File;" + eol +
                "//@ model import java.io.*;" + eol + eol +
                "class A {" + eol +
                "}"
        );
    }

    @Test
    public void testClassModifiers() {
        helpPP(
                eol + 
                "public static final class A {" + eol + 
                "}"
        );
    }
   
    @Test
    public void testMethodDecl() {
        helpPP(
                eol +
                "public static final class A {" + eol +
                "  " + eol + 
                "  void m() {" + eol +
                "  }" + eol +
                "}"
        );
    }
   
    @Test
    public void testMethodModifiers() {
        helpPP(
                eol + 
                "class A {" + eol + 
                "  " + eol + 
                "  public static void m() {" + eol +
                "  }" + eol +
                "}"
        );
    }
   
    @Test
    public void testMethodStatements() {
        precise = true;
        helpPP(
                eol + 
                "public static final class A {" + eol + 
                "  " + eol + 
                "  int p(int a, Object o) {" + eol +
                "  }" + eol +
                "  " + eol +
                "  void m() {" + eol +
                "    int a;" + eol +
                "    a = 5;" + eol +
                "    ;" + eol + 
                "    a += 5;" + eol +
                "    /*@ assume a == 6;*/" + eol +
                "    /*@ assert a == 6;*/" + eol +
                "    /*@ set a = 6;*/" + eol +
                "    /*@ set a = 6;*/" + eol +
                "    a += 5;" + eol +
                "    a -= 5;" + eol +
                "    a *= 5;" + eol +
                "    a /= 5;" + eol +
                "    a %= 5;" + eol +
                "    a |= 5;" + eol +
                "    a &= 5;" + eol +
                "    a ^= 5;" + eol +
                "    a <<= 5;" + eol +
                "    a >>= 5;" + eol +
                "    a >>>= 5;" + eol +
                "    m();" + eol +
                "    for (int i = 0; i < 5; i++) {" + eol +
                "    }" + eol +
                "    for (int i : new int[6]) {" + eol +
                "    }" + eol +
                "    while (true) {" + eol +
                "      do {" + eol +
                "      } while (true);" + eol +
                "    }" + eol +
                "    /*@ assert (* xyz *);*/" + eol +
                "  }" + eol +
                "}"
        );
    }
    
    @Test
    public void testMethodStatements2() {
        precise = false; // TODO  // Fixme - seems to use incorrectly formatted JML annotations 
        helpPP(
                eol + 
                "public static final class A {" + eol + 
                "  " + eol + 
                "  void m() {" + eol +
                "    int a;" + eol +
                "    a = 5;" + eol +
                "    ;" + eol + 
                "    a += 5;" + eol +
                "  }" + eol +
                "}"
        );
    }
    
    // FIXME - need to test every construct (lots more) for pretty printing; also for with and without jml comments
    
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
        helpAst(
            """
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
        helpAst(
            """
            public class A {
              static {
                int i = 7;
                i += 8;
                assert i == i;
              }
            }
            """);
    }
}
