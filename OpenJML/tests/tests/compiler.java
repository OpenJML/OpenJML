package tests;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.junit.Test;

import com.sun.tools.javac.util.Options;

import junit.framework.AssertionFailedError;
import junit.framework.TestCase;


public class compiler extends TestCase {

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
        //print = true;
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
     * @param exitcode the expected exit code (0=OK, 1=completed with error messages
     *      2=command-line problems, 3=system errors, 4=abort)
     * @param all whether the expected output is all of (0) or just the prefix
     *      of (1) or a part of (2) the actual output
     * @param output the expected output as one string
     */
    public void helper(String[] args, int exitcode, int all, String ... output) {
        int e = org.jmlspecs.openjml.Main.execute(args);
        savederr.flush();
        savedout.flush();
        System.setErr(savederr);
        System.setOut(savedout);
        // Depending on how the log is setup, error output can go to either bout or berr
        String actualOutput = berr.toString();
        //if (output.length <= 1 && actualOutput.length() == 0) actualOutput = bout.toString();
        if (actualOutput.length() == 0) actualOutput = bout.toString();
        if (print) System.out.println("EXPECTING: " + output[0]);
        if (capture) try {
            String tail = exitcode == 0 ? "" : "ENDING with exit code " + exitcode + eol;
            if (print) System.out.println("TEST: " + getName() + " exit=" + e + eol + actualOutput);
            String expected = output[0];
            if (all==0) assertEquals("The error message is wrong",expected+tail,actualOutput);
            else if (all == -1) assertEquals("The error message is wrong",expected,actualOutput);
            else if (all == 1 && !actualOutput.startsWith(expected)) {
                fail("Output does not begin with: " + expected + eol + "Instead is: " + actualOutput);
            } else if (all == 2 && actualOutput.indexOf(expected) == -1 ) {
                fail("Output does not end with: " + expected + eol + "Instead is: " + actualOutput);
            }
            if (output.length > 1) {
                expected = output[1];
                if (print) System.out.println("TEST: " + getName() + " STANDARD OUT: " + eol + bout.toString());
                if (all == 0) {
                    assertEquals("The standard out is wrong",expected+tail,bout.toString());
                } else if (all == -1) {
                    assertEquals("The standard out is wrong",expected,bout.toString());
                } else if (all == 2 && bout.toString().indexOf(expected) == -1) {
                    fail("Output does not end with: " + expected + eol + "Instead is: " + bout.toString());
                }
            }
            assertEquals("The exit code is wrong",exitcode,e);
        } catch (AssertionFailedError ex) {
            if (!print) System.out.println("TEST: " + getName() + " exit=" + e + eol + berr.toString());
            throw ex;
        }
    }

    @Test
    public void testTopLevelCompiler() throws Exception {
        String failureMessage = "error: The main entry point org.jmlspecs.openjml.Main.main was called with a null argument" + eol;
        helper(null,2,-1,failureMessage);
    }
    
    @Test
    public void testNoArgs() throws Exception {
        String failureMessage = "Usage: jml <options> <source files>" + eol +
                                "where possible options include:" + eol;
        helper(new String[]{},2,1,"",failureMessage);
    }
    
    @Test
    public void testBadOption() throws Exception {
        String failureMessage = "jml: invalid flag: -ZZZ" + eol +
                                "Usage: jml <options> <source files>" + eol + 
                                "use -help for a list of possible options" + eol;
        helper(new String[]{"-ZZZ"},2,0,failureMessage);
    }
    
    /** Tests setting the specs path through the command-line option, by using non-existent 
     * directories that then get complaints
     * @throws Exception
     */
    @Test
    public void testSpecPath() throws Exception {
        helper(new String[]
                  {"-classpath","cpath"+z+"cpath2","-sourcepath","spath","-specs","A"+z+"$SY"+z+"$CP"+z+"$SP"+z+"Z","A.java"},
                  2,
                  0,
                  "jml: file not found: A.java" + eol +
                  "Usage: jml <options> <source files>" + eol +
                  "use -help for a list of possible options" + eol +
                  "warning: A specification path directory does not exist: A" + eol +
                  "warning: A specification path directory does not exist: cpath" + eol +
                  "warning: A specification path directory does not exist: cpath2" + eol +
                  "warning: A specification path directory does not exist: spath" + eol +
                  "warning: A specification path directory does not exist: Z" + eol
                  );
    }
    
    @Test
    public void testRecursiveCP() throws Exception {
        helper(new String[]
                          { "-classpath","testfiles/testNoErrors"+z+"bin"+z+"$CP",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java",  
                          },0,0,"warning: $CP is included in the specs path recursively or multiple times"+eol
                          + "1 warning" + eol);
    }

    // TODO: Environment specific - backslashes
    @Test
    public void testNoRuntime() throws Exception {
        helper(new String[]
                          { "-noInternalRuntime","-noInternalSpecs",
                            "-classpath","testfiles/testNoErrors",
                            "testfiles/testNoErrors/A.java",  
                          },1,0,
                          "testfiles\\testNoErrors\\A.java:1: package org.jmlspecs.lang does not exist"+eol+
                          "public class A {" +eol+
                          "^"+eol+
                          "1 error" + eol+
                          "");
    }

    @Test
    public void testDuplicateParse() throws Exception {
        helper(new String[]
                          { "-classpath","testfiles/testNoErrors"+z+"bin",
                            "testfiles/testNoErrors/A.java", "-jmlverbose", "-noInternalSpecs" 
                          },0,2,"",
                          "parsing /home/projects/OpenJML/trunk/OpenJML/testfiles/testNoErrors/A.java" + eol +
                          "parsing /home/projects/OpenJML/trunk/OpenJML/testfiles/testNoErrors/A.refines-java" + eol +
                          "typechecking A" + eol +
                          "typechecked A" + eol +
                          //"flow checks A" + eol + 
                          "");
    }

    @Test
    public void testIgnoreJava() throws Exception {
        helper(new String[]
                          { "-classpath","testfiles/testJavaErrors"+z+"bin",
                            "testfiles/testJavaErrors/A.java", "-jmlverbose", "-noInternalSpecs"
                          },0,2,"",
                          "parsing /home/projects/OpenJML/trunk/OpenJML/testfiles/testJavaErrors/A.java" + eol +
                          "parsing /home/projects/OpenJML/trunk/OpenJML/testfiles/testJavaErrors/A.refines-java" + eol +
                          "typechecking A" + eol +
                          "typechecked A" + eol +
                          //"flow checks A" + eol + 
                          "");
    }

    @Test
    public void testSourcePath() throws Exception {
        helper(new String[]
                          { "-classpath","",
                            "-sourcepath","testfiles/testNoErrors"+z+"runtime",
                            "-specs","runtime",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    /** Tests using source path but including java spec files - may encounter
     * compilation warnings in the spec files as they evolve.
     * @throws Exception
     */
    @Test
    public void testSourcePathX() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath","testfiles/testNoErrors",
                            "-specs","runtime",
                            "-noPurityCheck",
                            "testfiles/testNoErrors/A.java"
                          },0,0,
                          "Note: Some input files use unchecked or unsafe operations."+eol+
                          "Note: Recompile with -Xlint:unchecked for details."+eol);
    }

    @Test
    public void testSourcePath3() throws Exception {
        helper(new String[]
                          { "-classpath","",
                            "-sourcepath","testfiles/testNoErrors"+z+"runtime",
                            "-specs","",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    // This test requires jmlruntime.jar to have been created - run the Makefile
    // in the OpenJML project
    @Test
    public void testSourcePath4() throws Exception {
        helper(new String[]
                          { "-classpath","jmlruntime.jar",
                            "-sourcepath","testfiles/testNoErrors",
                            "-specs","",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    @Test
    public void testSourcePath5() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath","testfiles/testNoErrors",
                            "-specs","",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java", 
                          },0,0,"",
                          "");
    }

//    @Test   FIXME - odd error message
//    public void testSourcePath2() throws Exception {
//        helper(new String[]
//                          { "-classpath","bin",
//                            "-sourcepath","testfiles/testNoErrors",
//                            "-specs","runtime",
//                            "-noInternalSpecs",
//                            "testfiles/testNoErrors/A.java"
//                          },1,0,"",  // FIXME - exit code should really be 0
//                          "");
//    }

    @Test
    public void testSuperRead() { // TODO - file name is environment dependent
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specs","testfiles",
                            "testfiles/testSuperRead/A.java"
                          },1,1
                          ,""
                          ,"testfiles\\testSuperRead\\B.refines-java:3: This JML modifier is not allowed for a type declaration"
                          );
    }
    
    
    // FIXME - need to check that the output of these two is correct
    
    @Test
    public void testAPI() {
        System.setErr(savederr);
        System.setOut(savedout);
        try {
            java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
            org.jmlspecs.openjml.API m = new org.jmlspecs.openjml.API(new String[]{});
            String s = m.prettyPrint(m.parseFiles(f).get(0),true);
            System.out.println(s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
        }
    }
    
    @Test
    public void testAPI2() {
        System.setErr(savederr);
        System.setOut(savedout);
        try {
            java.io.File f = new java.io.File("testfiles/testNoErrors/A.java");
            org.jmlspecs.openjml.API m = new org.jmlspecs.openjml.API(new String[]{"-v"});
            String s = m.prettyPrint(m.parseFiles(f).get(0),true);
            System.out.println(s);
        } catch (Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
        }
    }
}
