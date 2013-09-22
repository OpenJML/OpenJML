package tests;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TestName;

/** Tests running the tool as if from the command-line (for typechecking);
 * includes erroneous command-line argument combinations and combinations
 * of class, source, and specs paths. */
public class compiler {
    
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
    String projHome = System.getProperty("openjml.eclipseProjectLocation").replace("C:","").replace("\\","/");
    
    @Before
    public void setUp() throws Exception {
        //capture = false; print = true;
        savederr = System.err;
        savedout = System.out;
        if (capture) System.setErr(new PrintStream(berr=new ByteArrayOutputStream(10000)));
        if (capture) System.setOut(new PrintStream(bout=new ByteArrayOutputStream(10000)));
    }
    
    @After
    public void tearDown() {
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
        String actualOutput = bout.toString();
        String errOutput = berr.toString();
        actualOutput = actualOutput.toString().replace("\\","/");
        errOutput = errOutput.toString().replace("\\","/");
        if (print) System.out.println("EXPECTING: " + output[0]);
        if (print) System.out.println("ACTUAL OUT: " + actualOutput);
        if (print) System.out.println("ACTUAL ERR: " + errOutput);
        if (output.length <= 1 && errOutput.length() == 0 && !actualOutput.startsWith("Note:")) errOutput = actualOutput;
        if (capture) try {
            String tail = "";
            if (print) System.out.println("TEST: " + name.getMethodName() + " exit=" + e + eol + errOutput);
            String expected = output[0].replace("${PROJ}",projHome);
            if (all==0) assertEquals("The error message is wrong",expected+tail,errOutput);
            else if (all == -1) assertEquals("The error message is wrong",expected,errOutput);
            else if (all == 1 && !actualOutput.startsWith(expected)) {
                fail("Output does not begin with: " + expected + eol + "Instead is: " + errOutput);
            } else if (all == 2 && actualOutput.indexOf(expected) == -1 ) {
                fail("Output does not end with: " + expected + eol + "Instead is: " + errOutput);
            }
            if (output.length > 1) {
                expected = output[1].replace("${PROJ}",projHome);
                int k = actualOutput.indexOf("Note:");
                String actual = k>=0 ? actualOutput.substring(0,k) : actualOutput; 
                if (print) System.out.println("TEST: " + name.getMethodName() + " STANDARD OUT: " + eol + actual);
                if (all == 0) {
                    assertEquals("The standard out is wrong",expected+tail,actual);
                } else if (all == -1) {
                    assertEquals("The standard out is wrong",expected,actual);
                } else if (all == 1 && actualOutput.indexOf(expected) == -1) {
                    fail("Output does not end with: " + expected + eol + "Instead is: " + actual);
                }
            }
            assertEquals("The exit code is wrong",exitcode,e);
        } catch (AssertionError ex) {
            if (!print) System.out.println("TEST: " + name.getMethodName() + " exit=" + e + eol + berr.toString());
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
        String failureMessage = "Usage: openjml <options> <source files>" + eol +
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
    
    /** Tests a bad command */
    @Test
    public void testBadCommand() throws Exception {
        String failureMessage = "error: Invalid parameter to the -command option: zzz" + eol;
        helper(new String[]{"-command=zzz"},2,0,failureMessage);
    }
    
    /** Tests setting the specs path through the command-line option, by using non-existent 
     * directories that then get complaints
     * @throws Exception
     */
    @Test
    public void testSpecPath() throws Exception {
        helper(new String[]
                  {"-classpath","cpath"+z+"cpath2","-sourcepath","spath","-specspath","A"+z+"$SY"+z+"$CP"+z+"$SP"+z+"Z","-noPurityCheck","testfiles/testNoErrors/A.java"},
                  0,
                  1,
//                  "openjml: file not found: A.java" + eol +
//                  "Usage: openjml <options> <source files>" + eol +
//                  "use -help for a list of possible options" + eol +
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

    /** Tests the lack of a runtime library */
    @Test
    public void testNoRuntime() throws Exception {
        helper(new String[]
                          { "-noInternalRuntime","-noInternalSpecs",
                            "-classpath","testfiles/testNoErrors",
                            "testfiles/testNoErrors/A.java",  
                          },1,0,
                          "testfiles/testNoErrors/A.java:1: error: package org.jmlspecs.lang does not exist"+eol+
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
                          //"parsing ${PROJ}/testfiles/testNoErrors/A.java" + eol +
                          //"parsing ${PROJ}/testfiles/testNoErrors/A.refines-java" + eol +
                          "entering testfiles/testNoErrors/A.java" + eol +
                          "  completed entering testfiles/testNoErrors/A.java" + eol +
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
                          //"parsing ${PROJ}/testfiles/testJavaErrors/A.java" + eol +
                          // stuff about specs path comes in here
                          //"parsing ${PROJ}/testfiles/testJavaErrors/A.refines-java" + eol +
                          "entering testfiles/testJavaErrors/A.java" + eol +
                          "  completed entering testfiles/testJavaErrors/A.java" + eol +
                          "No specs for java.lang.annotation.Annotation" + eol +
                          "No specs for org.jmlspecs.annotation.Ghost" + eol +
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
                          { "-classpath"," ",
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
                          );
    }

    /** Tests using having a .jml file on the command line.
     * @throws Exception
     */ 
    @Test
    public void testJML() throws Exception {
        helper(new String[]
                          { "-classpath","runtime",
                            "-sourcepath","testfiles/testNoErrors",
                            "-specspath","runtime",
                            "-noPurityCheck",
                            "testfiles/testNoErrors/A.jml"
                          },0,0
                          ,""
                          );
    }

    /** Tests using having a .jml file on the command line, but the corresponding
     * Java file has a type error.
     * @throws Exception
     */ 
    @Test
    public void testJML1() throws Exception {
        print = true;
        helper(new String[]
                          { "-classpath","runtime",
                            "-sourcepath","testfiles/testJavaErrors2",
                            "-specspath","runtime"+z+"testfiles/testJavaErrors2",
                            "-noPurityCheck",
                            "testfiles/testJavaErrors2/A.java"
                          },1,1
                          ,"testfiles/testJavaErrors2/A.java:2: error: incompatible types"
                          );
    }

    /** Tests using having a .jml file on the command line, but the corresponding
     * Java file has a type error.
     * @throws Exception
     */ 
    @Test
    public void testJML1A() throws Exception {
        helper(new String[]
                          { "-classpath","runtime",
                            "-sourcepath","testfiles/testJavaParseErrors",
                            "-specspath","runtime"+z+"testfiles/testJavaParseErrors",
                            "-noPurityCheck",
                            "testfiles/testJavaParseErrors/A.jml"
                          },1,1
                          ,"testfiles/testJavaParseErrors/A.java:2: error: illegal start of expression"
                          );
    }

    /** Tests using having a .jml file on the command line, but the corresponding
     * Java file has a type error - but in the JML, so it is ignored since there 
     * already is a specs file.
     * @throws Exception
     */ 
    @Test
    public void testJML1B() throws Exception {
        helper(new String[]
                          { "-classpath","runtime",
                            "-sourcepath","testfiles/testJavaErrors",
                            "-specspath","runtime"+z+"testfiles/testJavaErrors",
                            "-noPurityCheck",
                            "testfiles/testJavaErrors/A.java"
                          },0,0,
                          ""
                          );
    }

    /** Tests using having a .jml file on the command line.
     * @throws Exception
     */ 
    @Test
    public void testJML2() throws Exception {
        helper(new String[]
                          { "-classpath","runtime",
                            "-sourcepath","testfiles/testNoSource",
                            "-specspath","runtime",
                            "-noPurityCheck",
                            "testfiles/testNoSource/A.jml"
                          },0,0
                          ,"warning: There is no java file on the sourcepath corresponding to the given jml file: testfiles/testNoSource/A.jml" + eol + "1 warning" + eol
                          );
    }

    /** Tests using having a .jml file on the command line.
     * @throws Exception
     */ 
    @Test
    public void testJML3() throws Exception {
        helper(new String[]
                          { "-classpath","runtime",
                            "-sourcepath"," ",
                            "-specspath","runtime",
                            "-noPurityCheck",
                            "testfiles/testNoErrors/A.jml"
                          },0,0
                          ,"warning: There is no java file on the sourcepath corresponding to the given jml file: testfiles/testNoErrors/A.jml" + eol + "1 warning" + eol
                          );
    }

    @Test
    public void testJML4() throws Exception {
        helper(new String[]
                          { "-classpath","runtime",
                            "-sourcepath"," ",
                            "-specspath","runtime",
                            "-noPurityCheck",
                            "testfiles/testNoSourceParseError/A.jml"
                          },1,0
                          ,"testfiles/testNoSourceParseError/A.jml:4: error: illegal start of expression" + eol +
                           "int i = ;" + eol +
                           "        ^" + eol +
                           "warning: There is no java file on the sourcepath corresponding to the given jml file: testfiles/testNoSourceParseError/A.jml" + eol + 
                           "1 error" + eol +
                           "1 warning" + eol
                          );
    }

    @Test
    public void testJML5() throws Exception {
        helper(new String[]
                          { "-classpath","runtime",
                            "-sourcepath"," ",
                            "-specspath","runtime",
                            "-noPurityCheck",
                            "testfiles/testNoSourceTypeError/A.jml"
                          },1,0
                          ,"warning: There is no java file on the sourcepath corresponding to the given jml file: testfiles/testNoSourceTypeError/A.jml" + eol +
                           "testfiles/testNoSourceTypeError/A.jml:4: error: incompatible types" + eol + 
                           "  Integer s = \"abc\";" + eol + 
                           "              ^" + eol +
                           "  required: Integer" + eol + 
                           "  found:    String" + eol +
                           "1 error" + eol +
                           "1 warning" + eol
                           );
    }

    // FIXME - the jml and class files do not match - we should get type errors
    @Test
    public void testJML6() throws Exception {
        helper(new String[]
                          { "-classpath","runtime"+z+"testfiles/testNoSourceWithClass",
                            "-sourcepath"," ",
                            "-specspath","runtime"+z+"testfiles/testNoSourceWithClass",
                            "-noPurityCheck",
                            "testfiles/testNoSourceWithClass/A.jml"
                          },0,0
                          ,"warning: There is no java file on the sourcepath corresponding to the given jml file: testfiles/testNoSourceWithClass/A.jml" + eol + "1 warning" + eol
                          );
    }

    /** Checks that -nowarn turns off waranings. */
    @Test
    public void testJML6nowarn() throws Exception {
        helper(new String[]
                          { "-classpath","runtime"+z+"testfiles/testNoSourceWithClass",
                            "-sourcepath"," ",
                            "-specspath","runtime"+z+"testfiles/testNoSourceWithClass",
                            "-noPurityCheck","-nowarn",
                            "testfiles/testNoSourceWithClass/A.jml"
                          },0,0
                          ,""
                          );
    }

    /** Checks that -Werror turns warnings into errors */
    @Test
    public void testJML6Werror() throws Exception {
        helper(new String[]
                          { "-classpath","runtime"+z+"testfiles/testNoSourceWithClass",
                            "-sourcepath"," ",
                            "-specspath","runtime"+z+"testfiles/testNoSourceWithClass",
                            "-noPurityCheck","-Werror",
                            "testfiles/testNoSourceWithClass/A.jml"
                          },1,0
                          ,"warning: There is no java file on the sourcepath corresponding to the given jml file: testfiles/testNoSourceWithClass/A.jml" + eol +
                           "error: warnings found and -Werror specified" + eol + 
                           "1 error" + eol + 
                           "1 warning" + eol);
    }

    /** Tests using source path but including java spec files - may encounter
     * compilation warnings in the spec files as they evolve.
     * Uses bin for classpath.
     * @throws Exception
     */
    @Test
    public void testSourcePathXB() throws Exception {
        helper(new String[]
                          { "-classpath","bin-runtime",  // FIXME - needs annotations?
                            "-sourcepath","testfiles/testNoErrors",
                            "-specspath","runtime",
                            "-noPurityCheck",  //"-Xlint:unchecked",
                            "testfiles/testNoErrors/A.java"
                          },0,0
                          ,""
                          );
    }

    /** Tests that specs files are not found with empty specs path */
    @Test
    public void testSourcePath3() throws Exception {
        helper(new String[]
                          { "-classpath"," ",
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
    //@Test  // FIXME - try running the build programmatically
    @Test 
    public void testSourcePath4() throws Exception {
        if (!new java.io.File("tempjars/jmlruntime.jar").exists()) {
            System.setErr(savederr);
            System.setOut(savedout);
            System.out.println("Starting");

//            org.eclipse.ant.core.AntRunner runner = new AntRunner();
//            //runner.setBuildFileLocation("C:/home/eclipse-workspace2/OpenJML/build-bash.xml");
//            runner.setBuildFileLocation("build-bash.xml");
//            System.out.println("Running? " + AntRunner.isBuildRunning());
//            runner.setArguments("-Dmessage=Building -verbose");
//            runner.setExecutionTargets(new String[]{"jmlruntime.jar"});
//            try {
//                runner.run();
//            } catch (Exception e) {
//                System.out.println("Exception " + e);
//                e.printStackTrace(System.out);
//            }

            //Process p = Runtime.getRuntime().exec("C:/home/apps/ant/apache-ant-1.7.1/bin/ant.cmd",new String[]{"-f","build-bash.xml","jmlruntime.jar"});
            //Process p = Runtime.getRuntime().exec("bash",new String[]{"C:/home/projects/OpenJML/trunk/OpenJML/buildRuntimelib"});
            //Process p = Runtime.getRuntime().exec("bash",new String[]{"buildRuntimelib"});
            //Process p = Runtime.getRuntime().exec("./buildRuntimelib");
//            System.out.println("Waiting");
//            StreamGobbler out = new StreamGobbler(p.getInputStream());
//            StreamGobbler err = new StreamGobbler(p.getErrorStream());
//            out.start(); err.start();
//            System.out.println("Waiting more");
//            boolean timedout = JmlTestCase.timeout(p,10000);
//            System.out.println("Timedout " + timedout);
//            if (!timedout) {
//                int e = p.waitFor();
//                System.out.println("Exit " + e);
//            }
            System.out.println("The testSourcePath4 test depends on having a release version of jmlruntime.jar in the jars directory.  It will not be run until a release has been built.");
        } else {
            helper(new String[]
                          { "-classpath","tempjars/jmlruntime.jar",
                            "-sourcepath","testfiles/testNoErrors",
                            "-specspath","",
                            "-noInternalSpecs",
                            "testfiles/testNoErrors/A.java",  
                          },0,0,"",
                          "");
        }
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
    public void testSuperRead() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "testfiles/testSuperRead/A.java"
                          },1,1
                          ,""
                          ,"testfiles/testSuperRead/B.jml:3: error: This JML modifier is not allowed for a type declaration"
                          );
    }
    
    /** Tests the -java option */
    @Test
    public void testJavaOption() {
        helper(new String[]
                          { "-java", 
                            "-classpath","testfiles",
                            "testfiles/testSpecErrors/A.java"
                          },0,0
                          ,""
                          ,"");
        
    }
    
    /** Tests the -java option must be first*/
    @Test
    public void testJavaOption2() {
        helper(new String[]
                          {  
                            "-classpath","testfiles",
                            "-java",
                            "-noPurityCheck",
                            "testfiles/testNoErrors/A.java"
                          },0,1
                          ,""
                          ,"The -java option is ignored unless it is the first command-line argument"
                          );
        
    }
    
    /** Tests that we get errors without the -java option */
    @Test
    public void testJavaOption1() {
        helper(new String[]
                          { "-classpath","testfiles/testSpecErrors", 
                            "-noPurityCheck",
                            "testfiles/testSpecErrors/A.java"
                          },1,0
                          ,""
                          ,"testfiles/testSpecErrors/A.jml:4: error: incompatible types" + eol + "    //@ ghost int i = true; // Error to provoke a message" + eol + "                      ^" + eol + "  required: int" + eol + "  found:    boolean" + eol + "1 error" + eol
                          );
    }
    
    /** Tests an invalid use of key */
    @Test
    public void testKeys0() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "testfiles/testKeys/D.java"
                          },0,0
                          ,""
                          ,""
                          );
    }
    
    /** Tests a single negative key that guards a line with an error */
    @Test
    public void testKeys1() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "testfiles/testKeys/A.java"
                          },1,1
                          ,"testfiles/testKeys/A.java:4: error: cannot find symbol"
                          ,""
                          );
    }
    
    /** Tests a single negative key that guards a line with an error */
    @Test
    public void testKeys1a() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "-keys","K2",
                            "testfiles/testKeys/A.java"
                          },1,1
                          ,"testfiles/testKeys/A.java:4: error: cannot find symbol"
                          ,""
                          );
    }
    
    /** Tests a single negative key that guards a line with an error */
    @Test
    public void testKeys2() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "-keys","K1",
                            "testfiles/testKeys/A.java"
                          },0,1
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys3() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "-keys","K2",
                            "testfiles/testKeys/B.java"
                          },1,1
                          ,"testfiles/testKeys/B.java:4: error: cannot find symbol"
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys4() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "testfiles/testKeys/B.java"
                          },0,0
                          ,""
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys4a() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "-keys","K3",
                            "testfiles/testKeys/B.java"
                          },0,0
                          ,""
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys5() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "-keys","K4,K2",
                            "testfiles/testKeys/C.java"
                          },0,0
                          ,""
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys6() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath","testfiles",
                            "-specspath","testfiles",
                            "-noPurityCheck",
                            "-keys","K2,K3",
                            "testfiles/testKeys/C.java"
                          },1,1
                          ,"testfiles/testKeys/C.java:10: error: cannot find symbol"
                          ,""
                          );
    }
    
    @Test
    public void testModelBug() throws Exception {
        helper(new String[]
                          { "-noPurityCheck",  //"-Xlint:unchecked",
                            "testfiles/model1/ModelClassExampleBug.java",
                            "testfiles/model1/ModelClassExampleBugSub.java",
                            "testfiles/model1/ModelClassExampleBugSub2.java"
                          },1,0
                          ,"testfiles/model1/ModelClassExampleBugSub.java:9: error: non-static type variable E cannot be referenced from a static context" + eol +
                           "    public static class SIndexedContents extends ModelClassExampleBug<E>.SContents { // ERROR" + eol +
                           "                                                                      ^" + eol +
                           "testfiles/model1/ModelClassExampleBugSub2.java:9: error: non-static type variable E cannot be referenced from a static context" + eol +
                           "        public static model class SMIndexedContents extends ModelClassExampleBug<E>.SMContents { // ERROR" + eol +
                           "                                                                                 ^" + eol +
                           "2 errors" + eol
                          );
    }

    @Test
    public void testModelBug2() throws Exception {
        helper(new String[]
                          { "-noPurityCheck",  //"-Xlint:unchecked",
                            "testfiles/model2/NonGenericModelClassExampleBug.java",
                            "testfiles/model2/NonGenericModelClassExampleBugSub.java",
                          },0,0
                          ,""
                          ,""
                          );
    }


}
