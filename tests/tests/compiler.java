package tests;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import junit.framework.AssertionFailedError;
import junit.framework.TestCase;

import org.junit.Test;


/** Tests running the tool as if from the command-line (for typechecking);
 * includes erroneous command-line argument combinations and combinations
 * of class, soruce, and specs paths. */
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
        //capture = false; print = true;
        super.setUp();
        savederr = System.err;
        savedout = System.out;
        if (capture) System.setErr(new PrintStream(berr=new ByteArrayOutputStream(10000)));
        if (capture) System.setOut(new PrintStream(bout=new ByteArrayOutputStream(10000)));
    }
    
    protected void tearDown() {
        // Do this just in case the test fails without having reset the streams
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
     * @param output the expected output as one string; if there are two Strings,
     * then they are the expected error and standard output 
     */
    public void helper(String[] args, int exitcode, int all, String ... output) {
        int e = org.jmlspecs.openjml.Main.execute(args);
        System.err.flush();
        System.out.flush();
        System.setErr(savederr);
        System.setOut(savedout);
        if (berr == null) return;
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

    /** Tests a null argument for the args */
    @Test
    public void testTopLevelCompiler() throws Exception {
        String failureMessage = "error: The main entry point org.jmlspecs.openjml.Main.main was called with a null argument" + eol;
        helper(null,2,-1,failureMessage);
    }
    
    /** Test with no arguments at all (empty array for args), which should
     * produce the help message. */
    @Test
    public void testNoArgs() throws Exception {
        String failureMessage = "Usage: jml <options> <source files>" + eol +
                                "where possible options include:" + eol;
        helper(new String[]{},2,1,"",failureMessage);
    }
    
    /** Tests an unknown option */
    @Test
    public void testBadOption() throws Exception {
        String failureMessage = "openjml: invalid flag: -ZZZ" + eol +
                                "Usage: openjml <options> <source files>" + eol + 
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
                  {"-classpath","cpath"+z+"cpath2","-sourcepath","spath","-specspath","A"+z+"$SY"+z+"$CP"+z+"$SP"+z+"Z","A.java"},
                  2,
                  0,
                  "openjml: file not found: A.java" + eol +
                  "Usage: openjml <options> <source files>" + eol +
                  "use -help for a list of possible options" + eol +
                  "warning: A specification path directory does not exist: A" + eol +
                  "warning: A specification path directory does not exist: cpath" + eol +
                  "warning: A specification path directory does not exist: cpath2" + eol +
                  "warning: A specification path directory does not exist: spath" + eol +
                  "warning: A specification path directory does not exist: Z" + eol
                  );
    }
    
    /** Tests a recursive definition for the specspath */
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
    /** Tests the lack of a runtime library */
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

    /** Test verbose with no specs used */
    @Test
    public void testDuplicateParse() throws Exception {
        helper(new String[]
                          { "-classpath","testfiles/testNoErrors"+z+"bin",
                            "testfiles/testNoErrors/A.java", "-jmlverbose", "-noInternalSpecs" 
                          },0,2,"",
                          "parsing /home/projects/OpenJML/trunk/OpenJML/testfiles/testNoErrors/A.java" + eol +
                          "parsing /home/projects/OpenJML/trunk/OpenJML/testfiles/testNoErrors/A.refines-java" + eol +
                          "entering A.java" + eol +
                          "  completed entering A.java" + eol +
                          "typechecking A" + eol +
                          "No specs for java.lang.Object" + eol + 
                          "typechecked A" + eol +
                          //"flow checks A" + eol + 
                          "");
    }

    /** Test that specs in the java file are ignored */
    @Test
    public void testIgnoreJava() throws Exception {
        helper(new String[]
                          { "-classpath","testfiles/testJavaErrors"+z+"bin",
                            "testfiles/testJavaErrors/A.java", "-jmlverbose", "-noInternalSpecs"
                          },0,2,"",
                          "parsing /home/projects/OpenJML/trunk/OpenJML/testfiles/testJavaErrors/A.java" + eol +
                          "parsing /home/projects/OpenJML/trunk/OpenJML/testfiles/testJavaErrors/A.refines-java" + eol +
                          "entering A.java" + eol +
                          "  completed entering A.java" + eol +
                          "typechecking A" + eol +
                          "No specs for java.lang.Object" + eol +
                          "typechecked A" + eol +
                          //"flow checks A" + eol + 
                          "");
    }

    /** Test that the source path is used to find input java files */
    @Test
    public void testSourcePath() throws Exception {
        helper(new String[]
                          { "-classpath","",
                            "-sourcepath","testfiles/testNoErrors"+z+"runtime",
                            "-specspath","runtime",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    /** Tests using source path but including java spec files - may encounter
     * compilation warnings in the spec files as they evolve.
     * Uses source for classpath.
     * @throws Exception
     */ // FIXME - clean up the unchecked casts
    @Test
    public void testSourcePathX() throws Exception {
        helper(new String[]
                          { "-classpath","runtime",
                            "-sourcepath","testfiles/testNoErrors",
                            "-specspath","runtime",
                            "-noPurityCheck",  //"-Xlint:unchecked",
                            "testfiles/testNoErrors/A.java"
                          },0,0
                          ,""
//                          ,"Note: Arrays.jml uses unchecked or unsafe operations."+eol+
//                           "Note: Recompile with -Xlint:unchecked for details."+eol
                          );
    }

    /** Tests using source path but including java spec files - may encounter
     * compilation warnings in the spec files as they evolve.
     * Uses bin for classpath.
     * @throws Exception
     */
    @Test
    public void testSourcePathXB() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath","testfiles/testNoErrors",
                            "-specspath","runtime",
                            "-noPurityCheck",  //"-Xlint:unchecked",
                            "testfiles/testNoErrors/A.java"
                          },0,0
                          ,""
//                          ,"Note: Arrays.jml uses unchecked or unsafe operations."+eol+
//                           "Note: Recompile with -Xlint:unchecked for details."+eol
                          );
    }

    /** Tests that specs files are not found with empty specs path */
    @Test
    public void testSourcePath3() throws Exception {
        helper(new String[]
                          { "-classpath","",
                            "-sourcepath","testfiles/testNoErrors"+z+"runtime",
                            "-specspath","",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    // This test requires jmlruntime.jar to have been created - run the Makefile
    // in the OpenJML project
    /** Tests using the runtime jar */
    @Test
    public void testSourcePath4() throws Exception {
        helper(new String[]
                          { "-classpath","jars/jmlruntime.jar",
                            "-sourcepath","testfiles/testNoErrors",
                            "-specspath","",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java",  
                          },0,0,"",
                          "");
    }

    /** Tests using class, source and specs path */
    @Test
    public void testSourcePath5() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath","testfiles/testNoErrors",
                            "-specspath","",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java", 
                          },0,0,"",
                          "");
    }

    @Test
    public void testSourcePath2() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath","testfiles/testNoErrors",
                            "-specspath","runtime",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java"
                          },0,0,"",
                          "");
    }

    /** Tests that super files are read and processed */
    @Test
    public void testSuperRead() { // TODO - file name is environment dependent
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "testfiles/testSuperRead/A.java"
                          },1,1
                          ,""
                          ,"testfiles\\testSuperRead\\B.refines-java:3: This JML modifier is not allowed for a type declaration"
                          );
    }
    

}
