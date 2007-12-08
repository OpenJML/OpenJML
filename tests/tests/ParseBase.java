package tests;

import java.util.LinkedList;
import java.util.List;

import junit.framework.AssertionFailedError;

import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlTreeScanner;

import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.parser.Parser;
import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.parser.Token;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Log;

/** This class is the base class for test suites that just are exercising the parser,
 * without doing any further typechecking.  FOr this purpose the parser can be
 * called standalone, and the parse tree inspected. 
 * @author David Cok
 *
 */
public class ParseBase extends JmlTestCase {

    static String z = java.io.File.pathSeparator;
    static String testspecpath = "$A"+z+"$B";

    Parser.Factory fac;
    Scanner.Factory sfac;
    Scanner sc;
    
    protected void setUp() throws Exception {
        super.setUp();
        options.put("compilePolicy","check");  // Don't do code generation
        options.put("-specs",   testspecpath);
        main.register(context);
        JmlEnter.instance(context); // Needed to avoid circular dependencies in tool constructors that only occur in testing
        Log.instance(context).multipleErrors = true;
        sfac = Scanner.Factory.instance(context);
        fac = Parser.Factory.instance(context);
        print = false;
    }

    protected void tearDown() throws Exception {
        super.tearDown();
        fac = null;
        sfac = null;
        sc = null;
    }

    /** Compiles the given string as the content of a compilation unit,
     * comparing the parse tree found to the expected node types and character
     * positions found in the second argument.
     * @param s the content of a compilation unit
     * @param list the expected parse tree formed by parsing the first argument
     * as a compilation unit, each node is represented by a node type (instance 
     * of Class) and character position (an int).
     */
    public void checkCompilationUnit(String s, Object ... list) {
        List<JCTree> out = parseCompilationUnit(s);
        checkParseTree(out,list);
    }

    // TODO - put in a few harness tests
    // TODO - test error messages
    public void checkCompilationUnitFailure(String failureMessage, String s, Object ... list) {
        boolean failed = false;
        try {
            checkCompilationUnit(s,list);
        } catch (AssertionFailedError a) {
            failed = true;
            assertEquals("Failure report wrong",failureMessage,a.getMessage());
        }
        if (!failed) fail("Test Harness failed to report an error");
    }
    
    /** Parses the content of a compilation unit, producing a list of nodes of
     * the parse tree
     * @param s the string to parse
     * @return the list of nodes in the resulting parse tree
     */
    public List<JCTree> parseCompilationUnit(String s) {
        Log.instance(context).useSource(new TestJavaFileObject(s));
        sc = sfac.newScanner(s);
        Parser p = fac.newParser(sc,false,true);
        JCTree e = p.compilationUnit();
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
                for (JCTree t: actual) {
                    System.out.println(t.getClass() + " " + t.getPreferredPosition());
                }
            }
            if (print) printErrors();
            if (actual.size()*2 != expected.length) {
                fail("Incorrect number of nodes listed " + (expected.length/2) + " vs. " + actual.size());
            }
            for (JCTree t: actual) {
                assertEquals("Class not matched at token " + k, expected[i++], t.getClass());
                assertEquals("Preferred position for token " + k, expected[i++], t.getPreferredPosition());
                ++k;
            }
            if (sc.token() != Token.EOF) fail("Not at end of input");
        } catch (AssertionFailedError e) {
            if (!print) printTree(actual);
            if (!print) printErrors();
            throw e;
        }
    }
    
    /** Prints out the nodes of the tree */
    public void printTree(List<JCTree> list) {
        System.out.println("NODES FOR " + getName());
        for (JCTree t: list) {
            System.out.println(t.getClass() + " " + t.getPreferredPosition());
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
         * super class method.
         */
        @Override
        public void scan(JCTree t) {
            if (t == null) return;
            list.add(t);
            super.scan(t);
        }
    }


    /** Just to avoid Junit framework complaints about no tests */
    public void test() {} 
}
