package org.jmlspecs.openjmltest;

import static org.junit.Assert.*;

import java.util.LinkedList;
import java.util.List;
import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.visitors.IJmlVisitor;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.openjml.MockJavaFileObject;

import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.parser.JmlFactory;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.ParserFactory;
import com.sun.tools.javac.parser.ScannerFactory;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Log;

/** This class is the base class for test suites that just are exercising the parser,
 * without doing any further typechecking.  For this purpose the parser can be
 * called standalone, and the parse tree inspected. 
 * @author David Cok
 *
 */
abstract public class ParseBase extends JmlTestSuite {

    /** This is used as a specspath consisting of mock files */
    protected static String testspecpath = "$A"+z+"$B";

    /** Just to hold this field between setup and use. */
    protected JmlFactory fac;
    /** Just to hold this field between setup and use. */
    protected JmlParser parser;

    /** Set this to true in tests which start out the scanner in jml mode
     * (avoiding the need to begin the test string with a JML comment annotation)
     */
    protected boolean jml;
    
    /** If true, do not check errors -- used primarily for harness tests */
    protected boolean skip = false;

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--specspath",   testspecpath);
        print = false;
        jml = false;
    }
    
    public void postOptions() {
        JmlAttr.instance(context); // Needed to avoid circular dependencies in tool constructors that only occur in testing
        JmlEnter.instance(context); // Needed to avoid circular dependencies in tool constructors that only occur in testing
        com.sun.tools.javac.code.JmlTypes.instance(context);
        com.sun.tools.javac.code.Symtab.instance(context);
        fac = (JmlFactory)JmlFactory.instance(context);
    }

    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        fac = null;
        parser = null;
    }

    /** Parse the given text (a compilation unit) and then compare any parse errors against 'expected'*/
    public void checkParseErrors(String text, Object ... expected) {
        if (skip) return;
        parseCompilationUnit(text);
        checkDiagnostics(expected);
    }

    /** Parses the content of a compilation unit, producing a list of nodes of
     * the parse tree
     * @param s the string to parse
     * @return the list of nodes in the resulting parse tree
     */
    public List<JCTree> parseCompilationUnit(String text) {
        // The following line sets the source material for error messages; the file name itself is immaterial
        Log.instance(context).useSource(new MockJavaFileObject(text));
        parser = fac.newParser(text, false, jml);
        parser.addOrgJmlspecsLang = false;
        JCTree e = parser.parseCompilationUnit();
        return ParseTreeScanner.walk(e);
    }


    /** Compares a list of nodes to the expected values given in the 
     * second argument; the second argument is expected to consist of the
     * class of a node (e.g. JCIdent.class) and the preferred character 
     * position of that node, for each element of the actual list.  The two 
     * lists are compared (both for node type and position) and JUnit failures
     * are raised for the first difference found.
     * @param actual a list of nodes as produced by ParseTreeScanner.walk
     * @param expected a list of expected data - class types and character positions
     * for each node in turn
     */
    public void checkParseTree(List<JCTree> actual, Object[] expected) {
        try {
            int i = 0;
            int k = 0;
            if (print) {
                printTree(actual);
                printDiagnostics();
            }
            Object p1, p2, p3;
            for (JCTree t: actual) {
                if (i>=expected.length) break;
                assertEquals("Class not matched at token " + k, expected[i++], t.getClass());
                p1 = expected[i++];
                p2 = (i < expected.length && expected[i] instanceof Integer) ? expected[i++] : null;
                p3 = (i < expected.length && expected[i] instanceof Integer) ? expected[i++] : null;
                if (p3 != null) {
                    assertEquals("Start position for token " + k, p1, t.getStartPosition());
                    assertEquals("Preferred position for token " + k, p2, t.getPreferredPosition());
                    assertEquals("End position for token " + k, p3, parser.getEndPos(t));
                } else if (p2 != null) {
                    assertEquals("Start position for token " + k, p1, t.getStartPosition());
                    assertEquals("End position for token " + k, p2, parser.getEndPos(t));
                } else {
                    assertEquals("Preferred position for token " + k, p1, t.getPreferredPosition());
                }
                ++k;
            }
            assertTrue("Insufficient number of nodes listed: expected " + k + ", was " + actual.size(), k == actual.size());
            assertEquals("Too many expected nodes listed", expected.length, i);
            // I don't believe that the following assert can ever fail -- the parser should keep going until the end of
            // input, continually emitting errors if needed.
            assertEquals("Not at end of input", TokenKind.EOF, parser.getScanner().token().kind);
        } catch (AssertionError e) {
            if (!print && !noExtraPrinting) {
                printTree(actual);
                printDiagnostics();
            }
            throw e;
        }
    }
    
    /** Prints out the nodes of the tree */
    public void printTree(List<JCTree> list) {
        out.println("NODES FOR " + getTestName()); // FIXME - test that this actually puts out the correct name
        for (JCTree t: list) {
            out.println(t.getClass() + " " + t.getStartPosition() + " " + t.getPreferredPosition() + " " + parser.getEndPos(t));
        }
    }

    /** A tree visitor class that walks the tree (depth-first), 
     * creating a list of the nodes it encounters.
     */
    static public class ParseTreeScanner extends JmlTreeScanner implements IJmlVisitor {
        /** The list of nodes */
        private List<JCTree> list = new LinkedList<JCTree>();;

        /** Constructs the visitor, but otherwise does nothing. */
        public ParseTreeScanner() {
        }

        /** A convenience method to walk the given tree and return the list of
         * its nodes.
         * @param tree the tree to be walked
         * @return the list of nodes in depth-first traversal order
         */
        static public List<JCTree> walk(JCTree tree) {
            ParseTreeScanner t = new ParseTreeScanner();
            t.scan(tree);
            return t.result();
        }

        /** Returns a reference to the list accumulated so far.
         * @return the accumulator list
         */
        public List<JCTree> result() { return list; }

        /** Adds a node to the internal accumulator and then calls the
         * super class method to continue to walk the tree.
         */
        @Override
        public void scan(JCTree t) {
            if (t == null) return;
            list.add(t);
            super.scan(t);
        }
    }
}
