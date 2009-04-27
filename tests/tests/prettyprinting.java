package tests;

import org.jmlspecs.openjml.JmlPretty;

import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Parser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Log;

/** This set of tests test that the pretty printer outputs properly.  The test
 * checks this by comparing the input code to the output code; before comparison,
 * each sequence of white space is replaced by a single space, so that the 
 * output formatting does not have to precisely match the input.
 */
public class prettyprinting extends ParseBase {

    boolean precise = false;
    @Override
    public void setUp() throws Exception {
        super.setUp();
        print = false;
    }

    public void helpPP(String code) {
        try {
            Log.instance(context).useSource(new TestJavaFileObject(code));
            Parser p = fac.newParser(code,false,true,true);
            //sc = ((JmlParser)p).getScanner();
            JCTree tree = p.parseCompilationUnit();
            String out = JmlPretty.write(tree);
            if (collector.getDiagnostics().size() != 0) printErrors();
            assertEquals("Found parsing errors",0,collector.getDiagnostics().size());
            if (!precise) {
                code = code.replaceAll("[ \t\r\n]+"," ");
                out = out.replaceAll("[ \t\r\n]+"," ");
            }
            if (print || !code.equals(out)) {
                System.out.println("IN:");
                System.out.print(code);
                System.out.println("OUT:");
                System.out.print(out);
                //printTree(ParseTreeScanner.walk(tree));
            }
            assertEquals("Output differs",code,out);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }
    
    String eol = System.getProperty("line.separator");

    public void testSimpleClass() {
        helpPP(
                eol +
                "class A { }"
        );
    }

    public void testPackage() {
        helpPP(
                "package t;" + eol + 
                "class A {" + eol +
                "}"
        );
    }

    public void testImport() {
        helpPP(
                "package t;" + eol + 
                "import java.io.File;" + eol +
                "class A {" + eol +
                "}"
        );
    }

    public void testImportStar() {
        helpPP(
                "package t;" + eol + 
                "import java.io.File;" + eol +
                "import java.io.*;" + eol +
                "class A {" + eol +
                "}"
        );
    }

    public void testModelImport() {
        helpPP(
                "package t;" + eol + 
                "//@ model import java.io.File;" + eol +
                "//@ model import java.io.*;" + eol +
                "class A {" + eol +
                "}"
        );
    }

    public void testRefines() {
        helpPP(
                "package t;" + eol + 
                "//@ refines \"A.jml\";" + eol + 
                "//@ model import java.io.File;" + eol +
                "//@ model import java.io.*;" + eol +
                "class A {" + eol +
                "}"
        );
    }
    
    public void testClassModifiers() {
        helpPP(
                eol + 
                "public static final class A {" + eol + 
                "}"
        );
    }
   
    public void testMethodDecl() {
        helpPP(
                eol +
                "public static final class A {" + eol + 
                "  void m() {" + eol +
                "  }" + eol +
                "}"
        );
    }
   
    public void testMethodModifiers() {
        helpPP(
                eol + 
                "class A {" + eol + 
                "  public static void m() {" + eol +
                "  }" + eol +
                "}"
        );
    }
   
    public void testMethodStatements() {
        precise = true;
        helpPP(
                eol + eol + 
                "public static final class A {" + eol + 
                "  " + eol + 
                "  " + eol +
                "  void m() {" + eol +
                "    " + eol +
                "    int a;" + eol +
                "    a = 5;" + eol +
                "    ;" + eol + 
                "    a += 5;" + eol +
                "    /*@ assume a == 6;*/" + eol +
                "    /*@ assert a == 6;*/" + eol +
                "    a += 5;" + eol +
                "  }" + eol +
                "}"
        );
    }
    
    // FIXME - need to test every construct
   
}
