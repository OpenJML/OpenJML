package tests;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import junit.framework.AssertionFailedError;
import junit.framework.TestCase;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.junit.Test;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCImport;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;


public class api extends TestCase {

    ByteArrayOutputStream berr;
    ByteArrayOutputStream bout;
    PrintStream savederr;
    PrintStream savedout;
    static String eol = System.getProperty("line.separator");
    static String z = java.io.File.pathSeparator;
    boolean print = false;
    boolean capture = true;
    
    protected void setUp() throws Exception {
        //capture = false; 
        super.setUp();
        savederr = System.err;
        savedout = System.out;
        if (capture) System.setErr(new PrintStream(berr=new ByteArrayOutputStream(10000)));
        if (capture) System.setOut(new PrintStream(bout=new ByteArrayOutputStream(10000)));
    }
    
    protected void tearDown() {
        berr = null;
        bout = null;
        System.setErr(savederr);
        System.setOut(savedout);
    }
    
    /** This is a helper method that runs the compiler on the given set of
     * command-line arguments, checking the result
     * @param args the command-line arguments
     * @param output the expected output as one string
     */
    
    public void start(boolean capture) {
        if (!capture) {
            System.err.flush();
            System.out.flush();
            System.setErr(savederr);
            System.setOut(savedout);
        }
        this.capture = capture;
    }
    
    public void check(String errOutput, String output) {
        if (!capture) return;
        System.err.flush();
        System.out.flush();
        System.setErr(savederr);
        System.setOut(savedout);
        // Depending on how the log is setup, error output can go to either bout or berr
        String actualErr = berr.toString();
        String actualOut = bout.toString();
        if (print) {
            System.out.println("TEST: " + getName());
            System.out.println("ERR: " + actualErr);
            System.out.println("OUT: " + actualOut);
        }
        if (capture && errOutput != null) try {
            compareStrings(errOutput,actualErr);
        } catch (AssertionFailedError ex) {
            if (!print) System.out.println("TEST: " + getName() + eol + actualErr);
            throw ex;
        }
        if (capture && output != null) try {
            compareStrings(output,actualOut);
        } catch (AssertionFailedError ex) {
            if (!print) System.out.println("TEST: " + getName() + eol + actualOut);
            throw ex;
        }
    }
    
    /** A helper routine to compare two Strings and instigating a JUnit test 
     * failure if they are different.  This differs from simple assertEquals
     * in giving more information about the point of difference.
     * @param expected The expected result
     * @param actual The actual result
     */
    public void compareStrings(String expected, String actual) {
        if (expected.equals(actual)) return;
        int i = 0;
        String msg = "";
        while (i < expected.length() && i < actual.length()) {
            if (expected.charAt(i) != actual.charAt(i)) {
                msg = msg + ("Strings differ at character " + i + " " + expected.charAt(i) + " vs. " + actual.charAt(i)) + eol;
            }
            i++;
        }
        if (expected.length() != actual.length()) msg = msg + ("Lengths differ " + expected.length() + " vs. " + actual.length()) + eol;
        assertEquals(msg,expected,actual);
    }
    

    
    
    String prettyprint =
        eol + 
        "public class A {" + eol +
        "  @Ghost " + eol +
        "  int i = 0;" + eol +
        "}" + eol +
        "// Refinement Sequence: testfiles/testNoErrors/A.java" + eol +
        "// Specification file: testfiles/testNoErrors/A.java" + eol +
        "" + eol +
        "public class A {" + eol +
        "  @Ghost " + eol +
        "  int i = 0;" + eol +
        "}" + eol;
    
    String prettyprint2 =
        eol + 
        "public class A {" + eol +
        "  @Ghost " + eol +
        "  int i = 0;" + eol +
        "}";
    
    /** Tests that a file parses and pretty prints */
    @Test
    public void testAPI() {
        start(true);
        try {
            java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
            org.jmlspecs.openjml.API m = new org.jmlspecs.openjml.API(new String[]{});
            String s = m.prettyPrint(m.parseFiles(f).get(0),true);
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assert(false);
        }
    }
    
    /** Tests that a file parses and pretty prints, using the no-argument
     * API constructor. */
    @Test
    public void testAPI1a() {
        start(true);
        try {
            java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
            org.jmlspecs.openjml.API m = new org.jmlspecs.openjml.API();
            String s = m.prettyPrint(m.parseFiles(f).get(0),true);
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assert(false);
        }
    }
    
    /** Tests that a file parses and pretty prints */
    @Test
    public void testAPI1z() {
        start(true);
        try {
            java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
            org.jmlspecs.openjml.API m = new org.jmlspecs.openjml.API();
            String s = m.prettyPrint(m.parseSingleFile(f),true);
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint2,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assert(false);
        }
    }
    
    /** Tests that a String parses and pretty prints */
    @Test
    public void testAPI1b() {
        start(true);
        try {
            String prog = "public class A { //@ ghost int i=0;\n }";
            org.jmlspecs.openjml.API m = new org.jmlspecs.openjml.API();
            String s = m.prettyPrint(m.parseString("A.java",prog),true);
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint2,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assert(false);
        }
    }
    
    /** Tests that a bad option is reported, but ignored */
    @Test
    public void testAPI2() {
        String output = 
            "openjml: invalid flag: -v" + eol +
            "Usage: openjml <options> <source files>" + eol +
            "use -help for a list of possible options" + eol;  
        start(true);
        try {
            java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
            org.jmlspecs.openjml.API m = new org.jmlspecs.openjml.API(new String[]{"-v"});
            String s = m.prettyPrint(m.parseFiles(f).get(0),true);
            check(output,"");
            s = s.replace('\\','/');
            compareStrings(prettyprint,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assert(false);
        }
    }
    
    /** This test builds an AST from a factory and then runs type checking 
     * on the AST.
     */
    @Test
    public void testAPI3() {
        String out =
            "package org.test;"+eol+
            eol+
            "import java.io.File;"+eol+
            "import java.math.*;"+eol+
            eol+
            "public class A {"+eol+
            "  protected int field = true;"+eol+
            "}"+eol;
        String err =
            "/A.java:1: incompatible types"+eol+
            "-------------"+eol+
            "^"+eol+
            "  required: int"+eol+
            "  found:    boolean"+eol+
            "/A.java:1: duplicate class: org.test.A"+eol+
            "-------------"+eol+
            "^"+eol;

        try {
            start(true);
            org.jmlspecs.openjml.API api = new org.jmlspecs.openjml.API("-noPurityCheck");//"jars/jmlruntime.jar");
            assertTrue(api.context != null);
            JmlTree.Maker f = JmlTree.Maker.instance(api.context);
            f.at(0);
            Names names = Names.instance(api.context);
            
            // protected int field = 5;
            JCModifiers mods2 = f.Modifiers(Flags.PROTECTED);
            Name field = Names.instance(api.context).fromString("field");
            JCExpression ty = f.TypeIdent(TypeTags.INT);
            JCExpression init = f.Literal(true);   // Intentional error
            JCVariableDecl vdecl = f.VarDef(mods2,field,ty,init);
            
            // The class declaration
            JCModifiers mods = f.Modifiers(Flags.PUBLIC);
            Name a = names.fromString("A");
            JCClassDecl cldef =
                f.ClassDef(mods,a,List.<JCTypeParameter>nil(),
                        null, // super class
                        List.<JCExpression>nil(), // List of super interfaces
                    List.<JCTree>of(vdecl));

            // An import statement
            JCExpression n = f.QualIdent(names.fromString("java"),
                    names.fromString("io"),
                    names.fromString("File"));
            JCExpression nn = f.QualIdent(names.fromString("java"),
                    names.fromString("math"),
                    names.asterisk);
            JCImport imp = f.Import(n,false); // import java.io.File; (false means not static)
            JCImport imp2 = f.Import(nn,false); // import java.math.*;
            
            // The compilation unit
            JCExpression packageid = f.QualIdent(names.fromString("org"),
                    names.fromString("test"));
            JmlCompilationUnit jcu = f.TopLevel(List.<JCAnnotation>nil(),
                                packageid,List.<JCTree>of(imp,imp2,cldef));
            jcu.mode = JmlCompilationUnit.JAVA_SOURCE_FULL;
            jcu.sourcefile = api.makeJFOfromString("A.java","-------------");
            // docCOmments, endPositions, flags, lineMap, mode, namedImportSCope,
            // parsedTopLevelModelTypes, starImportScope
            // refinesClause, specsTopLevelModelTypes, specsSequence
            
            // Javadoc comments
            Map<JCTree,String> doccomments = new HashMap<JCTree,String>();
            doccomments.put(cldef,"/** The class */");
            doccomments.put(vdecl,"/** The field */");
            jcu.docComments = doccomments;
            System.out.println(api.prettyPrint(jcu,false));
            
            Collection<JCTree> coll = new LinkedList<JCTree>();
            coll.add(jcu);
            int errs = api.enterAndCheck(jcu);
            errs += api.enterAndCheck(jcu);  // Complains about duplicate class
            check(err,out);
            assertEquals(2,errs);
            
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assert(false);
            
        }
    }
    
    /** Tests running a scanner over an AST */
    @Test
    public void testAPI4() {
        start(true);
        try {
            String program = "public class A { int i; }";
            org.jmlspecs.openjml.API m = new org.jmlspecs.openjml.API();
            JCTree ast = m.parseString("A.java",program);
            TestScanner v = new TestScanner();
            v.scanMode = v.AST_NO_MODEL_MODE;
            v.scan(ast);
            check("","");
            assertEquals(1,v.numberClasses);
            assertEquals(10,v.numberNodes);
            
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assert(false);
        }
    }
    
    public static class TestScanner extends JmlTreeScanner {
        public int numberClasses = 0;
        public int numberNodes = 0;
        
        public void scan(JCTree node) {
            numberNodes++;
            super.scan(node);  // Call this to scan child nodes
        }
        
        public void visitJmlClassDecl(JmlClassDecl node) {
            numberClasses++;
            super.visitJmlClassDecl(node); // Call this to scan child nodes
        }
    }

    // TODO: test copying; test different scan modes
    // TODO: need a way to reset the context
    // TODO: test getting specs and symbols
    // TODO: test combining specs
    // TODO: comments and javadoc comments
}