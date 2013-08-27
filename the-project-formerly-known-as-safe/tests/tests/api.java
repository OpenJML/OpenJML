package tests;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileReader;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.Factory;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TestName;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.comp.JmlEnter;
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


/** Tests the API class */
public class api {
    
    @Rule
    public TestName name = new TestName();

    ByteArrayOutputStream berr;
    ByteArrayOutputStream bout;
    PrintStream savederr;
    PrintStream savedout;
    static String eol = System.getProperty("line.separator");
    static String z = java.io.File.pathSeparator;
    boolean print = false;
    boolean capture = true;
    
    @Before
    public void setUp() throws Exception {
        //capture = false; 
        savederr = System.err;
        savedout = System.out;
        if (capture) System.setErr(new PrintStream(berr=new ByteArrayOutputStream(10000)));
        if (capture) System.setOut(new PrintStream(bout=new ByteArrayOutputStream(10000)));
    }
    
    @After
    public void tearDown() {
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
    
    public void endCapture() {
        if (!capture) return;
        System.err.flush();
        System.out.flush();
        System.setErr(savederr);
        System.setOut(savedout);
        capture = false;
    }
    
    public void check(String errOutput, String output) {
        if (!capture) return;
        boolean cap = capture;
        endCapture();
        // Depending on how the log is setup, error output can go to either bout or berr
        String actualErr = berr.toString();
        String actualOut = bout.toString();
        if (print) {
            System.out.println("TEST: " + name.getMethodName());
            System.out.println("ERR: " + actualErr);
            System.out.println("OUT: " + actualOut);
        }
        if (cap && errOutput != null) try {
            compareStrings(errOutput,actualErr);
        } catch (AssertionError ex) {
            if (!print) System.out.println("TEST: " + name.getMethodName() + eol + actualErr);
            throw ex;
        }
        if (cap && output != null) try {
            compareStrings(output,actualOut);
        } catch (AssertionError ex) {
            if (!print) System.out.println("TEST: " + name.getMethodName() + eol + actualOut);
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
        "  // JML specifications" + eol +
        "  @Ghost " + eol +
        "  int i = 0;" + eol +
        "}" + eol +
        "// Specifications: testfiles/testNoErrors/A.java" + eol +
        "// Specification file: testfiles/testNoErrors/A.java" + eol +
        "" + eol +
        "public class A {" + eol +
        "  // JML specifications" + eol +
        "  @Ghost " + eol +
        "  int i = 0;" + eol +
        "}" + eol;
    
    String prettyprint2 =
            eol + 
            "public class A {" + eol +
            "  // JML specifications" + eol +
            "  @Ghost " + eol +
            "  int i = 0;" + eol +
            "}";
        
    String prettyprint3 =
            "package a.b;" + eol +
            eol +
            "public class A {" + eol +
            "  // JML specifications" + eol +
            "  @Ghost " + eol +
            "  int i = 0;" + eol +
            "}";
        
    String parseAndPrettyPrintFromJavaFileObject() throws Exception {
        java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
        IAPI m = Factory.makeAPI(new String[]{});
        return m.prettyPrint(m.parseFiles(m.makeJFOfromFile(f)).get(0));
    }
    
    String parseAndPrettyPrintFromFile() throws Exception {
        java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseFiles(f).get(0));
    }
    
    String parseAndPrettyPrintFromMultipleFiles() throws Exception {
        java.io.File fa = new java.io.File("testfiles/testNoErrors/A.java");
        java.io.File fb = new java.io.File("testfiles/testNoErrors/B.java");
        IAPI m = Factory.makeAPI();
        java.util.List<org.jmlspecs.openjml.JmlTree.JmlCompilationUnit> asts = m.parseFiles(fa,fb);
        return m.prettyPrint(asts,"NEXT AST"); // Pretty prints a list of asts
    }

    String parseAndPrettyPrintFromFileArray() throws Exception {
        java.io.File fa = new java.io.File("testfiles/testNoErrors/A.java");
        java.io.File fb = new java.io.File("testfiles/testNoErrors/B.java");
        File[] files = new File[]{fa,fb};
        IAPI m = Factory.makeAPI();
        java.util.List<org.jmlspecs.openjml.JmlTree.JmlCompilationUnit> asts = m.parseFiles(files);
        return m.prettyPrint(asts,"NEXT AST"); // Pretty prints a list of asts
    }
    
    /** Tests that a file parses and pretty prints */
    // API(String[]), prettyPrint(JmlCompilationUnit, true), parseFiles
    @Test
    public void testParseAndPrettyPrint() {
        start(true);
        try {
            String s = parseAndPrettyPrintFromJavaFileObject();
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests that a file parses and pretty prints, using the no-argument
     * API constructor. */
    // API(), prettyPrint(JmlCompilationUnit, true), parseFiles
    @Test
    public void testParseAndPrettyPrint2() {
        start(true);
        try {
            String s = parseAndPrettyPrintFromFile();
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    @Test @Ignore  // FIXME - just haven't got the comparison string correct yet
    public void testParseAndPrettyPrint3() {
        start(true);
        try {
            String s = parseAndPrettyPrintFromMultipleFiles();
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    @Test @Ignore  // FIXME - just haven't got the comparison string correct yet
    public void testParseAndPrettyPrint4() {
        start(true);
        try {
            String s = parseAndPrettyPrintFromFileArray();
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    String parseAndPrettyPrintSingleFile() throws Exception {
        String f = "testfiles/testNoErrors/A.java";
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseSingleFile(f));
    }
    
    String parseAndPrettyPrintSingleFile2() throws Exception {
        IAPI m = Factory.makeAPI();
        JavaFileObject f = m.makeJFOfromFilename("testfiles/testNoErrors/A.java");
        return m.prettyPrint(m.parseSingleFile(f));
    }
    
    /** Tests that a file parses and pretty prints */
    // API(), prettyPrint(JmlCompilationUnit, true), parseSingleFile
    @Test
    public void testParseAndPrettyPrint5() {
        start(true);
        try {
            String s = parseAndPrettyPrintSingleFile();
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint2,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests that a file parses and pretty prints */
    // API(), prettyPrint(JmlCompilationUnit, true), parseSingleFile
    @Test
    public void testParseAndPrettyPrint5a() {
        start(true);
        try {
            String s = parseAndPrettyPrintSingleFile2();
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint2,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    @Test
    public void testAttach() {
        start(true);
        try {
            IAPI m = Factory.makeAPI("-noPurityCheck");
            String s1 = "public class A { /*@ ensures X;*/ void f() {} }";
            //String s2 = "public class A { /*@ requires Z; ensures Y;*/ void f(); }";
            JavaFileObject f1 = m.makeJFOfromString("A.java",s1);
            //JavaFileObject f2 = m.makeJFOfromString("A.jml",s2);
            JmlCompilationUnit ast1 = m.parseSingleFile(f1);
            //JmlCompilationUnit ast2 = m.parseSingleFile(f2);
            m.attachSpecs(ast1,ast1);
            int n = m.typecheck(ast1);
            endCapture();
            if (n != 1) {
                System.out.println("Errors: " + n);
                assertTrue(false);
            }
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    @Test
    public void testAttach2() {
        start(true);
        try {
            IAPI m = Factory.makeAPI("-noPurityCheck");
            String s1 = "public class A { /*@ ensures X;*/ void f() {} }";
            String s2 = "public class A { /*@ requires Z; ensures Y;*/ void f(); }";
            JavaFileObject f1 = m.makeJFOfromString("A.java",s1);
            JavaFileObject f2 = m.makeJFOfromString("A.jml",s2);
            JmlCompilationUnit ast1 = m.parseSingleFile(f1);
            JmlCompilationUnit ast2 = m.parseSingleFile(f2);
            m.attachSpecs(ast1,ast2);
            int n = m.typecheck(ast1);
            endCapture();
            if (n != 2) {
                System.out.println("Errors: " + n);
                assertTrue(false);
            }
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }

    @Test
    public void testAttach3() {
        start(true);
        try {
            IAPI m = Factory.makeAPI("-noPurityCheck");
            String s1 = "public class A { /*@ ensures true;*/ void f() {} }";
            JavaFileObject f1 = m.makeJFOfromString("A.java",s1);
            JmlCompilationUnit ast1 = m.parseSingleFile(f1);
            m.attachSpecs(ast1,null);
            int n = m.typecheck(ast1);
            endCapture();
            if (n != 0) {
                System.out.println("Errors: " + n);
                System.out.println(bout.toString());
                System.out.println(berr.toString());
                assertTrue(false);
            }
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    

    @Test
    public void testAttach5() {
        start(true);
        try {
            IAPI m = Factory.makeAPI("-noPurityCheck");
            String s1 = "public class A { void f() {} }";
            String s2 = "public class A { void g(); }";
            JavaFileObject f1 = m.makeJFOfromString("A.java",s1);
            JavaFileObject f2 = m.makeJFOfromString("A.jml",s2);
            JmlCompilationUnit ast1 = m.parseSingleFile(f1);
            JmlCompilationUnit ast2 = m.parseSingleFile(f2);
            m.attachSpecs(ast1,ast2);
            int n = m.typecheck(ast1);
            endCapture();
            // Should be one error - not checking what it is
            // (the .jml should not declare methods that are not in the .java file)
            if (n != 1) {
                System.out.println("Errors: " + n);
                assertTrue(false);
            }
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }


    String parseAndPrettyPrintString() throws Exception {
        String prog = "public class A { //@ ghost int i=0;\n }";
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseString("A.java",prog));
    }
    
    String parseAndPrettyPrintString2() throws Exception {
        String prog = "package a.b; public class A { //@ ghost int i=0;\n }";
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseString("a/b/A.java",prog));
    }
    
    /** Tests that a String parses and pretty prints */
    // API(), prettyPrint(JmlCompilationUnit, true), parseString
    @Test
    public void testParseAndPrettyPrint6() {
        start(true);
        try {
            String s = parseAndPrettyPrintString();
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint2,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests that a String parses and pretty prints */
    // API(), prettyPrint(JmlCompilationUnit, true), parseString
    @Test
    public void testParseAndPrettyPrint7() {
        start(true);
        try {
            String s = parseAndPrettyPrintString2();
            check("","");
            s = s.replace('\\','/');
            compareStrings(prettyprint3,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    String parseExpression() throws Exception {
        String expr = "a + b * c";
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseExpression(expr,false));
    }
    
    String parseJMLExpression() throws Exception {
        String expr = "a <==> \\result";
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseExpression(expr,true));
    }
    
    String parseStatement() throws Exception {
        String expr = "a = b;";
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseStatement(expr,false));
    }
    
    String parseStatement2() throws Exception {
        String expr = "while (true) {}";
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseStatement(expr,false));
    }
    
    String parseStatement3() throws Exception {
        String expr = "{ a=b; f(); }";
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseStatement(expr,false));
    }
    
    String parseJMLStatement2() throws Exception {
        String expr = "/*@ loop_invariant i < 10;*/";
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseStatement(expr,false));
    }
    
    String parseJMLStatement() throws Exception {
        String expr = "loop_invariant i >= 0;";
        IAPI m = Factory.makeAPI();
        return m.prettyPrint(m.parseStatement(expr,true));
    }
    
    /** Tests parsing an Expression */
    @Test
    public void testParseExpression() {
        start(true);
        try {
            String s = parseExpression();
            check("","");
            compareStrings("a + b * c",s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests parsing an Expression */
    @Test
    public void testParseJMLExpression() {
        start(true);
        try {
            String s = parseJMLExpression();
            check("","");
            compareStrings("a <==> \\result",s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests parsing a Statement */
    @Test
    public void testParseStatement() {
        start(true);
        try {
            String s = parseStatement();
            check("","");
            compareStrings("a = b;",s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests parsing a Statement */
    @Test
    public void testParseStatement2() {
        start(true);
        try {
            String s = parseStatement2();
            check("","");
            compareStrings("while (true) {" + eol + "}",s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests parsing a Statement */
    @Test
    public void testParseStatement3() {
        start(true);
        try {
            String s = parseStatement3();
            check("","");
            compareStrings("{" + eol + "  a = b;" + eol + "  f();" + eol + "}",s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests parsing a Statement */
    @Test
    public void testParseJMLStatement2() {
        start(true);
        try {
            String s = parseJMLStatement2();
            check("","");
            compareStrings("//@ loop_invariant i < 10;",s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests parsing a Statement */
    @Test
    public void testParseJMLStatement() {
        start(true);
        try {
            String s = parseJMLStatement();
            check("","");
            compareStrings("//@ loop_invariant i >= 0;",s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests that a bad option is reported, but ignored */
    // API(String), parseFiles, prettyPrint
    @Test
    public void testAPI2() {
        String output = 
            "openjml: invalid flag: -v" + eol +
            "Usage: openjml <options> <source files>" + eol +
            "use -help for a list of possible options" + eol;  
        start(true);
        try {
            Set<JavaFileObject> set = new HashSet<JavaFileObject>();
            IAPI m = Factory.makeAPI("-v");
            set.add(m.makeJFOfromFilename("testfiles/testNoErrors/A.java"));
            //String s = m.prettyPrint(m.parseFiles(set).get(0),true);
            check("",output);
            //s = s.replace('\\','/');
            //compareStrings(prettyprint,s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    // FIXME test API() with writer and diags; test exec; test version; test static execute
    
    /** This test builds an AST from a factory and then runs type checking 
     * on the AST.
     */
    // API(), nodeFactory(), context(), node building, prettyPrint(...,false), enterAndCheck(jcu)
    @Test
    public void testAPI3() {
      String out =
          "/A.java:1: error: incompatible types"+eol+
          "-------------"+eol+
          "^"+eol+
          "  required: int"+eol+
          "  found:    boolean"+eol+
          "/A.java:1: error: duplicate class: org.test.A"+eol+
          "-------------"+eol+
          "^"+eol;
      String err = "";

      try {
          start(true);
          IAPI api = Factory.makeAPI("-noPurityCheck");
          assertTrue(api.context() != null);
          JmlTree.Maker f = api.nodeFactory();
          f.at(0);
          
          // protected int field = 5;
          JCModifiers mods2 = f.Modifiers(Flags.PROTECTED);
          Name field = f.Name("field");
          JCExpression ty = f.TypeIdent(TypeTags.INT);
          JCExpression init = f.Literal(true);   // Intentional error
          JCVariableDecl vdecl = f.VarDef(mods2,field,ty,init);
          
          // The class declaration
          JCModifiers mods = f.Modifiers(Flags.PUBLIC);
          Name a = f.Name("A");
          JCClassDecl cldef =
              f.ClassDef(mods,a,List.<JCTypeParameter>nil(),
                      null, // super class
                      List.<JCExpression>nil(), // List of super interfaces
                  List.<JCTree>of(vdecl));

          // An import statement
          JCExpression n = f.QualIdent("java","io","File");
          JCExpression nn = f.QualIdent("java","math","*");
          JCImport imp = f.Import(n,false); // import java.io.File; (false means not static)
          JCImport imp2 = f.Import(nn,false); // import java.math.*;
          
          // The compilation unit
          JCExpression packageid = f.QualIdent("org","test");
          JmlCompilationUnit jcu = f.TopLevel(List.<JCAnnotation>nil(),
                              packageid,List.<JCTree>of(imp,imp2,cldef));
          jcu.mode = JmlCompilationUnit.JAVA_SOURCE_FULL;
          jcu.sourcefile = api.makeJFOfromString("A.java","-------------");
          // TODO: docCOmments, endPositions, flags, lineMap, mode, namedImportSCope,
          // parsedTopLevelModelTypes, starImportScope
          // refinesClause, specsTopLevelModelTypes, specsSequence
          
          // Javadoc comments
          Map<JCTree,String> doccomments = new HashMap<JCTree,String>();
          doccomments.put(cldef,"/** The class */");
          doccomments.put(vdecl,"/** The field */");
          jcu.docComments = doccomments;
          //System.out.println(api.prettyPrint(jcu,false));   //FIXME - doc comments do not print
          
          Collection<JmlCompilationUnit> coll = new LinkedList<JmlCompilationUnit>();
          coll.add(jcu);
          int errs = api.typecheck(coll);
          assertEquals(1,errs);
          
          java.util.List<JmlCompilationUnit> list = new LinkedList<JmlCompilationUnit>();
          list.add(jcu);
          errs += api.typecheck(list);  // Complains about duplicate class
          check(err,out);   //FIXME - i thought the default was  to send diags to System.out
          assertEquals(2,errs);
          
      } catch (Exception e) {
          check(null,null);
          System.out.println(e);
          e.printStackTrace(System.out);
      }
  }
  
    public void testAPI3a() {
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
          IAPI api = Factory.makeAPI(
                  new PrintWriter(System.err),null,null,"-noPurityCheck");
          assertTrue(api.context() != null);
          JmlTree.Maker f = api.nodeFactory();
          f.at(0);
          
          // protected int field = 5;
          JCModifiers mods2 = f.Modifiers(Flags.PROTECTED);
          Name field = f.Name("field");
          JCExpression ty = f.TypeIdent(TypeTags.INT);
          JCExpression init = f.Literal(true);   // Intentional error
          JCVariableDecl vdecl = f.VarDef(mods2,field,ty,init);
          
          // The class declaration
          JCModifiers mods = f.Modifiers(Flags.PUBLIC);
          Name a = f.Name("A");
          JCClassDecl cldef =
              f.ClassDef(mods,a,List.<JCTypeParameter>nil(),
                      null, // super class
                      List.<JCExpression>nil(), // List of super interfaces
                  List.<JCTree>of(vdecl));

          // An import statement
          JCExpression n = f.QualIdent("java","io","File");
          JCExpression nn = f.QualIdent("java","math","*");
          JCImport imp = f.Import(n,false); // import java.io.File; (false means not static)
          JCImport imp2 = f.Import(nn,false); // import java.math.*;
          
          // The compilation unit
          JCExpression packageid = f.QualIdent("org","test");
          JmlCompilationUnit jcu = f.TopLevel(List.<JCAnnotation>nil(),
                              packageid,List.<JCTree>of(imp,imp2,cldef));
          jcu.mode = JmlCompilationUnit.JAVA_SOURCE_FULL;
          jcu.sourcefile = api.makeJFOfromString("A.java","-------------");
          // TODO: docCOmments, endPositions, flags, lineMap, mode, namedImportSCope,
          // parsedTopLevelModelTypes, starImportScope
          // refinesClause, specsTopLevelModelTypes, specsSequence
          
          // Javadoc comments
          Map<JCTree,String> doccomments = new HashMap<JCTree,String>();
          doccomments.put(cldef,"/** The class */");
          doccomments.put(vdecl,"/** The field */");
          jcu.docComments = doccomments;
          System.out.println(api.prettyPrint(jcu));   //FIXME - doc comments do not print
          
          Collection<JmlCompilationUnit> coll = new LinkedList<JmlCompilationUnit>();
          coll.add(jcu);
          int errs = api.typecheck(coll);
          assertEquals(1,errs);
          
          java.util.List<JmlCompilationUnit> list = new LinkedList<JmlCompilationUnit>();
          list.add(jcu);
          errs += api.typecheck(list);  // Complains about duplicate class
          check(err,out);   //FIXME - i thought the default was  to send diags to System.out
          assertEquals(2,errs);
          
      } catch (Exception e) {
          check(null,null);
          System.out.println(e);
          e.printStackTrace(System.out);
          assertTrue(false);
      }
  }
  
    // TODOL test enterAndCheck with >1 arguments
    
    /** Tests running a scanner over an AST */
    // parseString, tree walking  // FIXME - document & test different scan modes
    @Test
    public void testAPI4() {
        start(true);
        try {
            String program = "public class A { int i; }";
            IAPI m = Factory.makeAPI();
            JCTree ast = m.parseString("A.java",program);
            TestScanner v = new TestScanner();
            v.scanMode = JmlTreeScanner.AST_JAVA_MODE;
            v.scan(ast);
            check("","");
            assertEquals(1,v.numberClasses);
            assertEquals(9,v.numberNodes);
            
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    @Test
    public void testAPI6() {
        start(true);
        try {
            IAPI m = Factory.makeAPI();
            int exitcode = m.execute(null,"-cp","testfiles/api","testfiles/api/A.java");
            assertTrue(exitcode == 0);
            assertTrue(m.isTypechecked("A"));
            assertTrue(!m.isTypechecked("B"));
            m.parseAndCheck(new File("testfiles/api/B.java"));
            assertTrue(m.isTypechecked("B"));
            ClassSymbol sym = m.getClassSymbol("B");
            m.doESC(sym);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        } finally {
            check("","");
        }
    }
    
    @Test
    public void testAPI5() {
        start(false);
        try {
            IAPI m = Factory.makeAPI("-verbose","-noInternalSpecs");
            int exitcode = m.execute(null,"-cp","testfiles/api","testfiles/api/A.java");
            assertTrue(exitcode == 0);
            assertTrue(m.isTypechecked("A"));
            assertTrue(!m.isTypechecked("B"));
            m.typecheck(m.parseFiles(new File("testfiles/api/B.java")));
            assertTrue(m.isTypechecked("B"));
            m.doESC(m.getClassSymbol("B"));
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        } finally {
            check("","");
        }
    }
    
    @Test
    public void testAPI7() {
        start(false);
        try {
            IAPI m = Factory.makeAPI("-verbose","-noInternalSpecs");
            int exitcode = m.execute(null,"-cp","testfiles/api2","testfiles/api2/p1/A.java");
            assertTrue(exitcode == 0);
            assertTrue(m.isTypechecked("p1.A"));
            assertTrue(!m.isTypechecked("p2.B"));
            m.typecheck(m.parseFiles(new File("testfiles/api2/p2/B.java")));
            assertTrue(m.isTypechecked("p2.B"));
            ClassSymbol sym = m.getClassSymbol("p2.B");
            sym = m.getClassSymbol("p2.B");
            m.doESC(sym);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        } finally {
            check("","");
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
    
    public boolean deleteAll(File f) {
        boolean b = true;
        if (!f.isDirectory()) {
            return f.delete();
        }
        for (File ff: f.listFiles()) {
            b = deleteAll(ff) && b;
        }
        return b;
    }
    
    /** Test jmldoc through the API */ // FIXME - this and maybe others do not check for errors
    // jmldoc
     @Ignore @Test // FIXME - disable until jmldoc is repaired
    public void testJmldoc() {
//        File f = new java.io.File("tempdoc");
//        if (f.exists()) {
//            boolean b = deleteAll(f);
//            assertTrue(b);
//        }
//        try {
//            int exitcode = API.jmldoc(new String[]{"-d","tempdoc","-notimestamp","-noPurityCheck","-dir","testfiles/jmldoc1/data"});
//            assertEquals("Mismatched exit code",0,exitcode);
//            // FIXME - run the diff program successfully, or do it programmatically
////            Process p = Runtime.getRuntime().exec("/usr/bin/diff",new String[]{"-r","-x",".svn","-x","package-tree.html","doc","../testfiles/jmldoc1/expected"});
////            exitcode = p.exitValue();
//            assertEquals(0,exitcode);
//        } catch (Exception e) {
//            fail();
//        }
    }

    public final static String program =
        "public class A { /*@ requires i > 0;*/void m(int i) {} void mm() { m(0); } int ff; int f; public static class B {} }";

    /** Tests the enterAndCheck call */
    // parseString, enterAndCheck
    @Test
    public void testEnterAndCheck() {
        start(true);
        try {
            IAPI m = Factory.makeAPI();
            m.addOptions("-noPurityCheck");
            JmlCompilationUnit jcu = m.parseString("A.java",program);
            int n = m.typecheck(jcu);
            check("","");
            assertTrue(n == 0);
        } catch(AssertionError e) {
            throw e;
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    @Test
    public void testOptions() {
        try {
            IAPI m = Factory.makeAPI();
            String s = m.getOption("-x");
            assertEquals(null,s);

            m.addOptions("-x");
            s = m.getOption("-x");
            assertEquals(null,s);

            m.main().addUncheckedOption("-x");
            s = m.getOption("-x");
            assertEquals("",s);

            m.addUncheckedOption("-x=asd");
            s = m.getOption("-x");
            assertEquals("asd",s);
            
            m.addUncheckedOption("-x=false");
            s = m.getOption("-x");
            assertEquals(null,s);
        } catch (Exception e) {
            fail();
        }
    }
    
    @Test
    public void testClose() {
        try {
            IAPI m = Factory.makeAPI();
            assertTrue(m.context() != null);
            m.close();
            assertTrue(m.context() == null);
        } catch (Exception e) {
            fail();
        }
    }

    // FIXME - test getting symbols by name with outer classes and inheritance
    
    /** Tests the symbol utilities call */
    // parseString, enterAndCheck, getClassSymbol, getSymbol, getClassDecl, getMethodDecl, getVarDecl
    @Test
    public void testSymbolUtilities() {
        start(true);
        try {
            IAPI m = Factory.makeAPI(new String[]{"-noPurityCheck"});
            JmlCompilationUnit jcu = m.parseString("A.java",program);
            int n = m.typecheck(new JmlCompilationUnit[]{jcu});
            assertTrue(n == 0);
            check("","");
            ClassSymbol csym = m.getClassSymbol("A");
            JmlClassDecl cd = m.getClassDecl(csym);
            JmlClassDecl cdd = m.getClassDecl("A");
            ClassSymbol csymm = m.getSymbol(cd);
            assertEquals(cd,cdd);
            assertEquals(csym,csymm);
            assertEquals("A",csym.className().toString());
            
            VarSymbol vsym = m.getVarSymbol(csym,"ff");
            assertEquals("ff",vsym.getSimpleName().toString());
            JmlVariableDecl vd = m.getVarDecl(vsym);
            VarSymbol vsymm = m.getSymbol(vd);
            assertEquals(vsym,vsymm);
            
            vsym = m.getVarSymbol(csym,"notexist");
            assertEquals(null,vsym);
            
            MethodSymbol msym = m.getMethodSymbol(csym,"mm");
            assertEquals("mm",msym.getSimpleName().toString());
            JmlMethodDecl md = m.getMethodDecl(msym);
            MethodSymbol msymm = m.getSymbol(md);
            assertEquals(msym,msymm);
            
            msym = m.getMethodSymbol(csym,"notexist");
            assertEquals(null,msym);
            
            ClassSymbol ccsym = m.getClassSymbol(csym,"B");
            assertEquals("B",ccsym.getSimpleName().toString());
            JmlClassDecl ccd = m.getClassDecl(ccsym);
            ClassSymbol ccsymm = m.getSymbol(ccd);
            assertEquals(ccsym,ccsymm);
            
            ccsym = m.getClassSymbol(csym,"notexist");
            assertEquals(null,ccsym);
            
            PackageSymbol psym = m.getPackageSymbol("java.lang");
            assertEquals("java.lang",psym.flatName().toString());
            psym = m.getPackageSymbol("org.jmlspecs.lang");
            assertEquals("org.jmlspecs.lang",psym.flatName().toString());
            psym = m.getPackageSymbol("org.jmlspecs.annotation");
            assertEquals("org.jmlspecs.annotation",psym.flatName().toString());
            psym = m.getPackageSymbol("");
            assertEquals("",psym.flatName().toString());
            psym = m.getPackageSymbol("ZZZ");
            assertEquals(null,psym);
            
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }


    /** Tests the parseAndCheck call */
    // parseAndCheck // FIXME test parseAndCheck with errors
    @Test
    public void testParseAndCheck() {
        start(true);
        try {
            java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
            IAPI m = Factory.makeAPI();
            m.addOptions("-noPurityCheck");
            m.parseAndCheck(f);
            check("","");
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests the parseAndCheck call */
    // parseAndCheck 
    @Test
    public void testParseAndCheckDuplicate() {
        start(true);
        try {
            DiagnosticCollector<JavaFileObject> dcoll = new DiagnosticCollector<JavaFileObject>();
            java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
            java.io.File ff = new java.io.File("testfiles/testNoErrors2/A.java");
            IAPI m = Factory.makeAPI(new PrintWriter(System.out),dcoll,null);
            m.addOptions("-noPurityCheck");
            m.parseAndCheck(f,ff);  // FIXME - expect errors - check for them
            check("","");
            java.util.List<Diagnostic<? extends JavaFileObject>> dlist = dcoll.getDiagnostics();
            int errs = dlist.size();
            assertEquals(1,errs);
            assertEquals("duplicate class: A",dlist.get(0).getMessage(null));
            assertEquals(8,dlist.get(0).getColumnNumber());
            assertEquals(1,dlist.get(0).getLineNumber());
            assertEquals(7,dlist.get(0).getPosition());
            assertEquals(0,dlist.get(0).getStartPosition());
            assertEquals(58,dlist.get(0).getEndPosition());
            assertEquals("testfiles/testNoErrors2/A.java",dlist.get(0).getSource().getName().toString().replace('\\','/'));
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests the parseAndCheck call */
    // parseAndCheck 
    @Test
    public void testParseAndCheckCrash() {
        start(true);
        String out = "error: A catastrophic JML internal error occurred.  Please report the bug with as much information as you can." + eol +
                "  Reason: The end-position table for testfiles\\testNoErrors\\A.java is set twice to different values" + eol;
        try {
            java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
            IAPI m = Factory.makeAPI();
            m.addOptions("-noPurityCheck");
            m.parseAndCheck(f,f);  // FIXME - duplicate entries causes crash
            check("","");
        } catch (Exception e) {
            check("",out);
//            System.out.println(e);
//            e.printStackTrace(System.out);
        }
    }
    
    /** Tests the parseAndCheck call */
    // parseAndCheck 
    @Test
    public void testParseAndCheck1Errors() {
        start(true);
        try {
            DiagnosticCollector<JavaFileObject> dcoll = new DiagnosticCollector<JavaFileObject>();
            java.io.File f = new java.io.File("testfiles/testSyntaxError/A.java");
            IAPI m = Factory.makeAPI(
                    new PrintWriter(System.out),dcoll,null);
            m.addOptions("-noPurityCheck");
            m.parseAndCheck(f); 
            check("","");
            java.util.List<Diagnostic<? extends JavaFileObject>> dlist = dcoll.getDiagnostics();
            int errs = dlist.size();
            assertEquals(3,errs);
            assertEquals("<identifier> expected",dlist.get(0).getMessage(null));
            assertEquals("reached end of file while parsing",dlist.get(1).getMessage(null));
            assertEquals("cannot find symbol\n  symbol:   class asdsadads\n  location: class A",dlist.get(2).getMessage(null));
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    
    /** Tests the parseAndCheck call */
    // parseAndCheck 
    // uses specs in the .jml file, not the .java file, so sees no errors
    @Test
    public void testParseAndCheck1ErrorsA() {
        start(true);
        try {
            DiagnosticCollector<JavaFileObject> dcoll = new DiagnosticCollector<JavaFileObject>();
            java.io.File f = new java.io.File("testfiles/testJavaErrors/A.java");
            IAPI m = Factory.makeAPI(
                    new PrintWriter(System.out),dcoll,null,
                    "-specspath","testfiles/testJavaErrors");
            m.addOptions("-noPurityCheck");
            m.parseAndCheck(f); 
            check("",""); // FIXME - this does not capture errors
            java.util.List<Diagnostic<? extends JavaFileObject>> dlist = dcoll.getDiagnostics();
            int errs = dlist.size();
            assertEquals(0,errs);
            //assertEquals("testfiles\\testJavaErrors\\A.java:2: incompatible types\n  required: int\n  found:    boolean",((JCDiagnostic)dlist.get(0)).noSource());
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests the parseAndCheck call */
    // parseAndCheck 
    // No specspath so uses the .java file, which has an error
    @Test
    public void testParseAndCheck1ErrorsB() {
        start(true);
        try {
            DiagnosticCollector<JavaFileObject> dcoll = new DiagnosticCollector<JavaFileObject>();
            java.io.File f = new java.io.File("testfiles/testJavaErrors/A.java");
            IAPI m = Factory.makeAPI(
                    new PrintWriter(System.out),dcoll,null);
            m.addOptions("-noPurityCheck");
            m.parseAndCheck(f); 
            check("","");
            java.util.List<Diagnostic<? extends JavaFileObject>> dlist = dcoll.getDiagnostics();
            int errs = dlist.size();
            assertEquals(1,errs);
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests the parseAndCheck call */
    // parseAndCheck 
    @Test
    public void testParseAndCheck1ErrorsC() {
        start(true);
        try {
            DiagnosticCollector<JavaFileObject> dcoll = new DiagnosticCollector<JavaFileObject>();
            java.io.File f = new java.io.File("testfiles/testSpecErrors/A.java");
            IAPI m = Factory.makeAPI(
                    new PrintWriter(System.out),dcoll,null);
            m.addOptions("-noPurityCheck");
            //m.addOptions("-specspath","testfiles/testSpecErrors");
            m.parseAndCheck(f); 
            check("","");
            java.util.List<Diagnostic<? extends JavaFileObject>> dlist = dcoll.getDiagnostics();
            int errs = dlist.size();
            assertEquals(0,errs);
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    @Test
    public void testParseAndCheck1ErrorsD() {
        start(true);
        try {
            DiagnosticCollector<JavaFileObject> dcoll = new DiagnosticCollector<JavaFileObject>();
            java.io.File f = new java.io.File("testfiles/testSpecErrors/A.java");
            IAPI m = Factory.makeAPI(
                    new PrintWriter(System.out),dcoll,null,"-specspath","testfiles/testSpecErrors");
            m.addOptions("-noPurityCheck");
            m.parseAndCheck(f); 
            check("","");
            java.util.List<Diagnostic<? extends JavaFileObject>> dlist = dcoll.getDiagnostics();
            int errs = dlist.size();
            assertEquals(1,errs);
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    @Test
    public void testParseAndCheck1ErrorsE() {
        start(true);
        try {
            DiagnosticCollector<JavaFileObject> dcoll = new DiagnosticCollector<JavaFileObject>();
            java.io.File f = new java.io.File("testfiles/testSpecErrors/A.java");
            IAPI m = Factory.makeAPI(
                    new PrintWriter(System.out),dcoll,null);
            m.addOptions("-noPurityCheck");
            m.addOptions("-specspath","testfiles/testSpecErrors");
            m.parseAndCheck(f); 
            check("","");
            java.util.List<Diagnostic<? extends JavaFileObject>> dlist = dcoll.getDiagnostics();
            int errs = dlist.size();
            assertEquals(1,errs);
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests the parseAndCheck call */
    // parseAndCheck 
    @Test
    public void testParseAndCheck2() {
        start(true);
        try {
            java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
            IAPI m = Factory.makeAPI();
            m.addOptions("-noPurityCheck");
            m.parseAndCheck(new File[]{f});
            check("","");
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    // FIXME _ also test various solvers
    
    @Test
    public void testESC() {
        testESC("-newesc");
    }
    
    @Test @Ignore
    public void testESCBoogie() {
        testESC("-boogie");
    }
    
    

    /** Tests ESC */
    // doESC [all variations, with and without errors]
    // getClassSymbol, getMethodSymbol, getProofResult
    public void testESC(String option) {
        start(false);
        try {
            DiagnosticCollector<JavaFileObject> diags = new DiagnosticCollector<JavaFileObject>();
            IAPI m = Factory.makeAPI(
                    new PrintWriter(System.out),
                    diags,
                    null,
                    option,
                    "-noPurityCheck");
//            if (option.equals("-custom")) {
//                m.addOptions("openjml.defaultProver","yices");
//            } else 
            if (option.equals("-boogie")) {
                m.addOptions("openjml.defaultProver","z3_4_3");
            } else {
                m.addOptions("openjml.defaultProver","z3_4_3");
            }
            JmlCompilationUnit jcu = m.parseString("A.java",program);
            int n = m.typecheck(jcu);
            assertTrue(n==0);
            ClassSymbol csym = m.getClassSymbol("A");
            MethodSymbol mmsym = m.getMethodSymbol(csym,"mm");
            MethodSymbol msym = m.getMethodSymbol(csym,"m");

            IProverResult res = m.doESC(msym);
            java.util.List<Diagnostic<? extends JavaFileObject>> dlist = diags.getDiagnostics();
            if (dlist.size() != 0) { // Should be none
                // Print out observed errors for debugging
                endCapture();
                for (Diagnostic<? extends JavaFileObject> d: dlist) {
                    System.out.println(d.getMessage(null));
                }
            }
            //res = m.getProofResult(msym);
            assertTrue(res != null);
            assertEquals(0,dlist.size());
            assertEquals(IProverResult.UNSAT,res.result());

            res = m.doESC(mmsym);
            endCapture();
            //res = m.getProofResult(mmsym);
            assertTrue(res != null);
            assertEquals(2,dlist.size());
            assertTrue(res.result() == IProverResult.POSSIBLY_SAT || res.result() == IProverResult.SAT);
            
            m.doESC(csym);
            check("","");
            assertEquals(4,dlist.size());
        } catch(AssertionError e) {
            throw e;
        } catch (Exception e) {
            check("","");
            System.out.println(e);
            e.printStackTrace(System.out);
            assertTrue(false);
        }
    }
    
    /** Tests the makeJFO... methods */
    // makeJFO...
    @Test
    public void testUtils() {
        try {
            IAPI api = Factory.makeAPI();
            char[] cb = new char[10000];
            FileReader fr = new FileReader(new File("testfiles/testNoErrors/A.java"));
            int n = fr.read(cb,0,cb.length);
            fr.close();
            if (n == -1) fail("Failed to read A.java");
            if (n == cb.length) fail("Buffer not large enough");
            String fc = new String(cb,0,n);
            JavaFileObject jfo = api.makeJFOfromFilename("testfiles/testNoErrors/A.java");
            assertEquals(JavaFileObject.Kind.SOURCE,jfo.getKind());
            assertEquals(fc,jfo.getCharContent(true).toString());
            jfo = api.makeJFOfromString("A.java","public class A{}");
            assertEquals(JavaFileObject.Kind.SOURCE,jfo.getKind());
            assertEquals("public class A{}",jfo.getCharContent(true).toString());
            jfo = api.makeJFOfromString("A.jml","public class A{}");
            assertEquals(JavaFileObject.Kind.OTHER,jfo.getKind());
            assertEquals("public class A{}",jfo.getCharContent(true).toString());
            jfo = api.makeJFOfromFile(new File("testfiles/testNoErrors/A.java"));
            assertEquals(JavaFileObject.Kind.SOURCE,jfo.getKind());
            assertEquals(fc,jfo.getCharContent(true).toString());
        } catch(AssertionError e) {
            throw e;
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail();
        }
    }


    // TODO: test setProgressReporter, exec
    // TODO: test enterAndCheck with multiple arguments
    // TODO: test parseFiles with multiple File arguments
    // TODO: test parseFiles with multiple JavaFileObject arguments
    // TODO: test getBasicBlockPRogram
    // TODO: test collectSuperTypes, collectSuperMethods
    // TODO: test getSpecs, getAllSpecs for field, method, class
    // TODO: test getting denested specs
    // TODO: test prettyprint on list
    // TODO: what about making mock JFO directories and specspath entries
    // TODO: test getCEValue
    
    // TODO: test copying; test different scan modes
    // TODO: need a way to reset the context
    // TODO: test getting specs and symbols
    // TODO: test combining specs
    // TODO: comments and javadoc comments
}