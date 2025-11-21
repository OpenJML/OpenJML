package org.jmlspecs.openjmltest.testsuites;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.jmlspecs.openjmltest.JmlTestSuite;
import org.junit.After;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TestName;

// FIXME - compare to release tests!!!!!!
// FIXME - these tests set various static stuff (System.out, System.err, Main.useJML) -- how is this thread safe?

/** Tests running the tool as if from the command-line (for typechecking);
 * includes erroneous command-line argument combinations and combinations
 * of class, source, and specs paths. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class compiler extends JmlTestSuite{
    
    public static final String relsrc = "releaseTests/src";
    public static final String src = "test/compiler/";
    
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
    String projHome;
    {
        String h = System.getProperty("openjml.eclipseProjectLocation");
        if (h == null) h = JmlTestSuite.root + "/OpenJML21/OpenJMLTest";
        projHome = h.replace("C:","").replace("\\","/");
    }
    String specsHome;
    {
    	try {
    		specsHome = JmlTestSuite.root + "/Specs";
    	} catch (Exception e) {
    		specsHome = null;
    	}
    }
    String expectedFile = null;
    
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
     * @param expectedExitCode the expected exit code (0=OK, 1=completed with error messages
     *      2=command-line problems, 3=system errors, 4=abort)
     * @param all whether the expected output is all of (0) or just the prefix
     *      of (1) or a part of (2) the actual output
     * @param output the expected output as one string; if there are two Strings,
     * then they are the expected error and standard output 
     */
    public void helper(String[] args, int expectedExitCode, int all, String ... output) {
        int exitCode;
        try {
            exitCode = org.jmlspecs.openjml.Main.execute(args);
        } finally {
            System.err.flush();
            System.out.flush();
            System.setErr(savederr);
            System.setOut(savedout);
        }
        if (berr == null) return;
        // Depending on how the log is setup, error output can go to either bout or berr
        String actualOutput = bout.toString();
        String errOutput = berr.toString();
        actualOutput = actualOutput.replace("\\","/");
        //actualOutput = actualOutput.replaceAll("temp-release/", "");
        errOutput = errOutput.toString().replace("\\","/");

        String expected;
        if (expectedFile != null) {
            try {
                expected = new String(java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(expectedFile)));
                expected = JmlTestSuite.doReplacements(expected.replace("./src",relsrc));
            } catch (Exception ee) {
                expected = null;
                org.junit.Assert.fail(ee.toString());
            }
        } else {
            expected = output[0];
        }
        expected = JmlTestSuite.doReplacements(expected.replace("${PROJ}",projHome));
        actualOutput = actualOutput.replace("\r", "");
        errOutput = errOutput.replace("\r", "");
        expected = expected.replace("\r", "");
        actualOutput = removeNotes(actualOutput);

        if (print) System.out.println("EXPECTING: " + output[0]);
        print = false;
        if (print) System.out.println("ACTUAL OUT: " + actualOutput);
        if (print) System.out.println("ACTUAL ERR: " + errOutput);
        if (output.length <= 1 && errOutput.length() == 0 && !actualOutput.startsWith("Note:")) errOutput = actualOutput;
        if (capture) try {
            String tail = "";
            if (print) System.out.println("TEST: " + getTestName() + " exit=" + exitCode + eol + errOutput);
            if (all==0) assertEquals("The error message is wrong",expected+tail,errOutput);
            else if (all == -1) assertEquals("The error message is wrong",expected,errOutput);
            else if (all == 1 && !actualOutput.startsWith(expected)) {
                fail("Output does not begin with: " + expected + eol + "Instead is: " + errOutput);
            } else if (all == 2 && actualOutput.indexOf(expected) == -1 ) {
                fail("Output does not end with: " + expected + eol + "Instead is: " + errOutput);
            }
            if (output.length > 1) {
                expected = output[1].replace("${PROJ}",projHome).replaceAll("\r", "");
                int k = actualOutput.indexOf("Note:");
                String actual = k>=0 ? actualOutput.substring(0,k) : actualOutput; 
                if (print) System.out.println("TEST: " + getTestName() + " STANDARD OUT: " + eol + actual);
                if (all == 0) {
                    assertEquals("The standard out is wrong",expected+tail,actual);
                } else if (all == -1) {
                    assertEquals("The standard out is wrong",expected,actual);
                } else if (all == 1 && (actualOutput.indexOf(expected) == -1 && errOutput.indexOf(expected) == -1)) {
                    fail("Output does not contain: " + expected + eol + "Instead is: " + actual);
                }
            }
            assertEquals("The exit code is wrong",expectedExitCode,exitCode);
        } catch (AssertionError ex) {
            if (!print) {
                System.out.println("TEST: " + getTestName() + " exit=" + exitCode + eol + berr.toString());
                System.out.println("ACTUAL OUT: " + actualOutput);
                System.out.println("ACTUAL ERR: " + errOutput);
            }
            throw ex;
        }
    }
    
    public String removeNotes(String input) {
        while (true) {
        	int p = input.indexOf("Note: ");
        	if (p < 0) break;
        	int q = input.indexOf("\n",p);
        	input = input.substring(0, p) + input.substring(q+1);
        }
        return input;
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
                                "Use option '-?' to list options" + eol;
        helper(new String[]{},2,1,"",failureMessage);
    }
    
    /** Tests an unknown option */
    @Test
    public void testBadOption() throws Exception {
        String failureMessage = "error: invalid flag: -ZZZ" + eol +
                                "Usage: openjml <options> <source files>" + eol + 
                                "use --help for a list of possible options" + eol;
        helper(new String[]{"-ZZZ",src + "testNoErrors/A.java"},2,0,failureMessage);
    }
    
    /** Tests a bad command */
    @Test
    public void testBadCommand() throws Exception {
        String failureMessage = "error: Invalid parameter to the --command option: zzz" + eol;
        helper(new String[]{"-command=zzz",src + "testNoErrors/A.java"},2,0,failureMessage);
    }
    
    /** Tests setting the specs path through the command-line option, by using non-existent 
     * directories that then get complaints
     * @throws Exception
     */
    @Test
    public void testSpecPath() throws Exception {
        helper(new String[]
                  {"-classpath","cpath"+z+"cpath2",
                   "-sourcepath","spath",
                   "--specs-path","A"+z+"$SY"+z+"$CP"+z+"$SP"+z+"Z",
                   "--no-purity-check",
                   src + "testNoErrors/A.java"},
                  0,
                  1,
//                  "openjml: file not found: A.java" + eol +
//                  "Usage: openjml <options> <source files>" + eol +
//                  "use -help for a list of possible options" + eol +
                  "warning: A specification path directory does not exist: A ($ROOT/OpenJML/OpenJMLTest)" + eol +
                  "warning: A specification path directory does not exist: cpath ($ROOT/OpenJML/OpenJMLTest)" + eol +
                  "warning: A specification path directory does not exist: cpath2 ($ROOT/OpenJML/OpenJMLTest)" + eol +
                  "warning: A specification path directory does not exist: spath ($ROOT/OpenJML/OpenJMLTest)" + eol +
                  "warning: A specification path directory does not exist: Z ($ROOT/OpenJML/OpenJMLTest)" + eol
                  );
    }
    
    /** Tests a recursive definition for the specspath */
    @Test
    public void testRecursiveCP() throws Exception {
        helper(new String[]
                          { "-classpath",src + "testNoErrors"+z+"$CP",
                            src + "testNoErrors/A.java",  
                          },0,0,"warning: $CP is included in the specs path recursively or multiple times"+eol
                          + "1 warning" + eol);
    }

    /** Tests the lack of a runtime library */
    @Test @Ignore // FIXME: Current implementation cannot disable the internal runtime library
    public void testNoRuntime() throws Exception {
        helper(new String[]
                          { 
                            "-classpath",src + "testNoErrors",
                            src + "testNoErrors/A.java",  
                          },3,0,
                          "Fatal Error: Unable to find package org.jmlspecs.lang" + eol);
//                          src + "testNoErrors/A.java:1: error: package org.jmlspecs.lang does not exist"+eol+
//                          "public class A {" +eol+
//                          "^" + eol +
//                          "1 error" + eol);
    }

    /** Test verbose with no specs used */
    @Test
    public void testDuplicateParse() throws Exception {
        helper(new String[]
                          { "-classpath",src + "testNoErrors"+z+"bin",
                            src + "testNoErrors/A.java", "-jmlverbose" 
                          },0,2,"",
                          //"parsing ${PROJ}/test/testNoErrors/A.java" + eol +
                          //"parsing ${PROJ}/test/testNoErrors/A.refines-java" + eol +
                          "entering test/testNoErrors/A.java" + eol +
                          "  completed entering test/testNoErrors/A.java" + eol +
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
                          { "-classpath",src + "testJavaErrors"+z+"bin",
                            src + "testJavaErrors/A.java"
                          },0,2,"",
                          //"parsing ${PROJ}/test/testJavaErrors/A.java" + eol +
                          // stuff about specs path comes in here
                          //"parsing ${PROJ}/test/testJavaErrors/A.refines-java" + eol +
                          "entering test/testJavaErrors/A.java" + eol +
                          "  completed entering test/testJavaErrors/A.java" + eol +
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
                            "-sourcepath",src + "testNoErrors",
                            src + "testNoErrors/A.java",  
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
                          { "-classpath",JmlTestSuite.runtime,
                            "-sourcepath",src + "testNoErrors",
                            "--no-purity-check",  //"-Xlint:unchecked",
                            src + "testNoErrors/A.java"
                          },0,0
                          ,""
                          );
    }

    /** Tests using having a .jml file on the command line.
     * @throws Exception
     */   // FIXME - may want to figure out how to act on the jml files
    @Test
    public void testJML() throws Exception {
        helper(new String[]
                          { "-classpath",JmlTestSuite.runtime,
                            "-sourcepath",src + "testNoErrors",
                            "--no-purity-check",
                            src + "testNoErrors/A.jml"
                          },2,0
                          ,""
                          ,"warning: .jml files on the command-line are ignored: " + src + "testNoErrors/A.jml" + eol +
                           "error: no source files" + eol
                          );
    }

    /** Tests using having a .jml file on the command line, but the corresponding
     * Java file has a type error.
     * @throws Exception
     */ 
    @Test
    public void testJML1() throws Exception {
        //print = true;
        helper(new String[]
                          { "-classpath",JmlTestSuite.runtime,
                            "-sourcepath",src + "testJavaErrors2",
                            "--specs-path",src + "testJavaErrors2",
                            "--no-purity-check",
                            src + "testJavaErrors2/A.java"
                          },1,1
                          ,src + "testJavaErrors2/A.java:2: error: incompatible types"
                          );
    }

    /** Tests using having a .jml file on the command line, but the corresponding
     * Java file has a type error.
     * @throws Exception
     */ 
    @Test
    public void testJML1A() throws Exception {
        helper(new String[]
                          { "-classpath",JmlTestSuite.runtime,
                            "-sourcepath",src + "testJavaParseErrors",
                            "--specs-path",src + "testJavaParseErrors",
                            "--no-purity-check",
                            src + "testJavaParseErrors/A.jml"
                          },2,1
                          ,""
                          ,"error: no source files" + eol
                          //,src + "testJavaParseErrors/A.java:2: error: illegal start of expression"
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
                          { "-classpath",JmlTestSuite.runtime,
                            "-sourcepath",src + "testJavaErrors",
                            "--specs-path",src + "testJavaErrors",
                            "--no-purity-check",
                            src + "testJavaErrors/A.java"
                          },0,0,
                          ""
                          );
    }

    /** Tests having a .jml file on the command line.
     * @throws Exception
     */ 
    @Test
    public void testNoSource() throws Exception {
        helper(new String[]
                          { "-classpath",JmlTestSuite.runtime,
                            "-sourcepath",src + "testNoSource",
                            "--specs-path",JmlTestSuite.runtime,
                            "--no-purity-check",
                            src + "testNoSource/A.jml"
                          },2,1
                          ,""
                          ,"error: no source files" + eol
                          //,"error: There is no java or binary file on the sourcepath corresponding to the given jml file: test/testNoSource/A.jml" + eol 
                          );
    }

    /** Tests using having a .jml file on the command line.
     * @throws Exception
     */ 
    @Test
    public void testNoErrors() throws Exception {
        helper(new String[]
                          { "-classpath",JmlTestSuite.runtime,
                            "-sourcepath"," ",
                            "--specs-path",JmlTestSuite.runtime,
                            "--no-purity-check",
                            src + "testNoErrors/A.jml"
                          },2,1
                          ,""
                          ,"error: no source files" + eol
                          //,"error: There is no java or binary file on the sourcepath corresponding to the given jml file: test/testNoErrors/A.jml" + eol
                          );
    }

    @Test
    public void testNoSourceParseError() throws Exception {
        helper(new String[]
                          { "-classpath",JmlTestSuite.runtime,
                            "-sourcepath"," ",
                            "--specs-path",JmlTestSuite.runtime,
                            "--no-purity-check",
                            src + "testNoSourceParseError/A.jml"
                          },2,1
                          ,""
                          ,"error: no source files" + eol
//                        ,src + "testNoSourceParseError/A.jml:4: error: illegal start of expression" + eol +
//                           "int i = ;" + eol +
//                           "        ^" + eol +
//                           "error: There is no java or binary file on the sourcepath corresponding to the given jml file: test/testNoSourceParseError/A.jml" + eol
                          );
    }

    @Test
    public void testNoSourceTypeError() throws Exception {
        helper(new String[]
                          { "-classpath",JmlTestSuite.runtime,
                            "-sourcepath"," ",
                            "--specs-path",JmlTestSuite.runtime,
                            "--no-purity-check",
                            src + "testNoSourceTypeError/A.jml"
                          },2,1
                          ,""
                          ,"error: no source files" + eol
                           );
    }

    // FIXME - the jml and class files do not match - we should get type errors
    // FIXME - jml files on command-line are ignored
    @Test
    public void testNoSourceWithClass() throws Exception {
        helper(new String[]
                          { "-classpath", JmlTestSuite.runtime +z+src + "testNoSourceWithClass",
                            "-sourcepath"," ",
                            "--specs-path", JmlTestSuite.runtime +z+src + "testNoSourceWithClass",
                            "--no-purity-check",
                            src + "testNoSourceWithClass/A.jml"
                          },2,1
                          ,""
                          ,"error: no source files" + eol 
                          );
    }

    /** Checks that -nowarn turns off warnings. */
    @Test
    public void testWarnings() throws Exception {
        helper(new String[]
                                { "-nowarn", 
                                  src + "testWarnings/A.java"
                                },0,0
                                ,""
                                );
    }

    /** Checks that -Werror turns warnings into errors */  // FIXME - not working
    @Test
    public void testJML6Werror() throws Exception {
        helper(new String[]
                                { "-Werror",
                                  src + "testWarnings/A.java"
                                },1,0
                                ,""
                                ,src + "testWarnings/A.java:3: warning: There is no point to a specification case having more visibility than its method"+eol
                                +"  //@ public normal_behavior"+eol
                                +"      ^"+eol
                                +"error: warnings found and -Werror specified"+eol
                                +"1 error"+eol
                                +"1 warning"+eol
                                );
    }

    /** Checks that -Werror turns warnings into errors */
    @Test
    public void testJML6WerrorA() throws Exception {
        helper(new String[]
                                { "-Werror",
                                  "--specs-path",src + "testNoErrors", // protects against spec errors in A.java
                                  src + "testWarnings/A.java"
                                },0,0
                                ,""
                                ,""
                                );
    }

    /** Checks that -Werror turns warnings into errors */  // FIXME - not working
    @Test
    public void testJML6WerrorB() throws Exception {
        helper(new String[]
                                { "-Werror",
                                  "-sourcepath",src + "testNoErrors", // is also the spec path, so protects against spec errors in A.java
                                  "--specs-path","",
                                  src + "testWarnings/A.java"
                                },0,0
                                ,""
                                ,""
                                );
    }

    /** Checks that -Werror turns warnings into errors */  // FIXME - not working
    @Test
    public void testJML6WerrorC() throws Exception {
        helper(new String[]
                                { "-Werror",
                                  "-sourcepath",src + "testNoErrors", // is also the spec path, so protects against spec errors in A.java
                                  "-classpath",JmlTestSuite.bruntime, // does not exist, but isnot part of the specs path
                                  src + "testWarnings/A.java"
                                },0,0
                                ,""
                                ,""
                                );
    }

    /** Checks that -Werror turns warnings into errors */  // FIXME - not working
    @Test
    public void testJML6WerrorD() throws Exception {
        helper(new String[]
                                { "-Werror",
                                  "-classpath", JmlTestSuite.bruntime, // does not exist, but isnot part of the specs path
                                  src + "testWarnings/A.java"
                                },1,0
                                ,""
                                ,"warning: A specification path directory does not exist: " + JmlTestSuite.bruntime + " (" + JmlTestSuite.root + "/OpenJML/OpenJMLTest)"+eol
                                +"error: warnings found and -Werror specified"+eol
                                +"1 error"+eol
                                +"1 warning"+eol
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
                          { "-classpath", JmlTestSuite.bruntime,  // FIXME - needs annotations?
                            "-sourcepath",src + "testNoErrors",
                            "--specs-path","../../Specs/specs",
                            "--no-purity-check",  //"-Xlint:unchecked",
                            src + "testNoErrors/A.java"
                          },0,0
                          ,""
                          );
    }

//    /** Tests that specs files are not found with empty specs path */
//    @Test
//    public void testSourcePath3() throws Exception {
//        helper(new String[]
//                          { "-classpath"," ",
//                            "-sourcepath",src + "testNoErrors"+z+runtime,
//                            src + "testNoErrors/A.java",  
//                          },0,0,"",
//                          "");
//    }

    // This test requires jmlruntime.jar to have been created - run the Makefile
    // in the OpenJML project
    /** Tests using the runtime jar */
    //@Test  // FIXME - try running the build programmatically
    @Test 
    public void testSourcePath4() throws Exception {
        if (!new java.io.File("../OpenJML21/release-temp/jmlruntime.jar").exists()) {
            System.setErr(savederr);
            System.setOut(savedout);
            System.out.println("The testSourcePath4 test depends on having a release version of jmlruntime.jar in the jars directory.  It will not be run until a release has been built.");
        } else {
            helper(new String[]
                          { "-classpath","../OpenJML21/release-temp/jmlruntime.jar",
                            "-sourcepath",src + "testNoErrors",
                            "--specs-path","",
                            src + "testNoErrors/A.java",  
                          },0,0,"",
                          "");
        }
    }

    /** Tests using class, source and specs path */
    @Test
    public void testSourcePath5() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath",src + "testNoErrors",
                            "--specs-path","",
                            src + "testNoErrors/A.java", 
                          },0,0,"",
                          "");
    }

    @Test
    public void testSourcePath2() throws Exception {
        helper(new String[]
                          { "-classpath","bin",
                            "-sourcepath",src + "testNoErrors",
                            src + "testNoErrors/A.java"
                          },0,0,"",
                          "");
    }

    /** Tests that super files are read and processed */
    @Test
    public void testSuperRead() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath",src,
                            "--specs-path",src,
                            "--no-purity-check",
                            src + "testSuperRead/A.java"
                          },1,1
                          ,""
                          ,src + "testSuperRead/B.jml:3: error: This JML modifier is not allowed for a type declaration"
                          );
    }
    
    // Tests of -java are in runscripts.javaOnly. They cannot be part of a 
    // test suite because they set the static field Utils.isjml
    
    /** Tests an invalid use of key */
    @Test
    public void testKeys() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath",src,
                            "--specs-path",src,
                            "--no-purity-check",
                            src + "testKeys/D.java"
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
                            "-sourcepath",src,
                            "--specs-path",src,
                            "--no-purity-check",
                            src + "testKeys/A.java"
                          },1,1
                          ,src + "testKeys/A.java:4: error: cannot find symbol"
                          ,""
                          );
    }
    
    /** Tests a single negative key that guards a line with an error */
    @Test
    public void testKeys1a() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath",src,
                            "--specs-path",src,
                            "--no-purity-check",
                            "-keys","K2",
                            src + "testKeys/A.java"
                          },1,1
                          ,src + "testKeys/A.java:4: error: cannot find symbol"
                          ,""
                          );
    }
    
    /** Tests a single negative key that guards a line with an error */
    @Test
    public void testKeys2() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath",src,
                            "--specs-path",src,
                            "--no-purity-check",
                            "-keys","K1",
                            src + "testKeys/A.java"
                          },0,1
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys3() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath",src,
                            "--specs-path",src,
                            "--no-purity-check",
                            "-keys","K2",
                            src + "testKeys/B.java"
                          },1,1
                          ,src + "testKeys/B.java:4: error: cannot find symbol"
                          ,""
                          );
    }
    
    /** Tests a single positive key that guards a line with an error */
    @Test
    public void testKeys4() {
        helper(new String[]
                          { "-classpath","bin", 
                            "-sourcepath",src,
                            "--specs-path",src,
                            "--no-purity-check",
                            src + "testKeys/B.java"
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
                            "-sourcepath",src,
                            "--specs-path",src,
                            "--no-purity-check",
                            "-keys","K3",
                            src + "testKeys/B.java"
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
                            "-sourcepath",src,
                            "--specs-path",src,
                            "--no-purity-check",
                            "-keys","K4,K2",
                            src + "testKeys/C.java"
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
                            "-sourcepath",src,
                            "--specs-path",src,
                            "--no-purity-check",
                            "-keys","K2,K3",
                            src + "testKeys/C.java"
                          },1,1
                          ,src + "testKeys/C.java:10: error: cannot find symbol"
                          ,""
                          );
    }
    
    /** Tests an unmatched quote */
    @Test
    public void testBadEqual() {
        helper(new String[]
                          { "--zzz=yyy"
                          },2,0
                          ,""
                          ,"""
                           error: invalid flag: --zzz=yyy
                           Usage: openjml <options> <source files>
                           use --help for a list of possible options
                           """
                          );
    }
    
    /** Tests an unmatched quote */
    @Test
    public void testOrphanQuote() {
        helper(new String[]
                          { "\""
                          },2,0
                          ,""
                          ,"""
                           error: invalid flag: "
                           Usage: openjml <options> <source files>
                           use --help for a list of possible options
                           """
                          );
    }
    
    /** Tests an unmatched quote with content */
    @Test
    public void testOrphanQuote2() {
        helper(new String[]
                          { "\"--check"
                          },2,0
                          ,""
                          ,"""
                           error: invalid flag: "--check
                           Usage: openjml <options> <source files>
                           use --help for a list of possible options
                           """
                          );
    }
    
    @Test
    public void testModelBug() throws Exception {
        helper(new String[]
                          { "--no-purity-check",  //"-Xlint:unchecked",
                            src+"testModelBug/ModelClassExampleBug.java",
                            src+"testModelBug/ModelClassExampleBugSub.java",
                            src+"testModelBug/ModelClassExampleBugSub2.java"
                          },1,0
                          ,""
                          ,src+"testModelBug/ModelClassExampleBugSub.java:9: error: non-static type variable E cannot be referenced from a static context" + eol +
                           "    public static class SIndexedContents extends ModelClassExampleBug<E>.SContents { // ERROR" + eol +
                           "                                                                      ^" + eol +
                           src+"testModelBug/ModelClassExampleBugSub2.java:9: error: non-static type variable E cannot be referenced from a static context" + eol +
                           "        public static model class SMIndexedContents extends ModelClassExampleBug<E>.SMContents { // ERROR" + eol +
                           "                                                                                 ^" + eol +
                           src+"testModelBug/ModelClassExampleBugSub.java:9: error: cannot select a static class from a parameterized type" + eol +
                           "    public static class SIndexedContents extends ModelClassExampleBug<E>.SContents { // ERROR" + eol +
                           "                                                                        ^" + eol +
                           src+"testModelBug/ModelClassExampleBugSub2.java:9: error: cannot select a static class from a parameterized type" + eol +
                           "        public static model class SMIndexedContents extends ModelClassExampleBug<E>.SMContents { // ERROR" + eol +
                           "                                                                                   ^" + eol +
                           "4 errors" + eol
                          );
    }
    
    @Test
    public void testOptionLang() {
        helper(new String[] {"--lang=zzz","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: Command-line argument error: Expected one of [jml, openjml] for --lang: zzz
                1 warning
                """);
    }

    @Test
    public void testOptionLang0() {
        helper(new String[] {"--lang=\"\"","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: Command-line argument error: Expected one of [jml, openjml] for --lang: ""
                1 warning
                """);
    }

    @Test
    public void testOptionLang1() {
        helper(new String[] {"--lang=\" \"","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: Command-line argument error: Expected one of [jml, openjml] for --lang: " "
                1 warning
                """);
    }

    @Test
    public void testOptionLang2() {
        helper(new String[] {"\"--lang= \"","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                "warning: Command-line argument error: Expected one of [jml, openjml] for --lang:  \n1 warning\n"
                );
    }

    @Test
    public void testOptionLang3() {
        helper(new String[] {"--lang=","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionArith() {
        helper(new String[] {"--arithmetic-failure=zzz","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: The value of the --arithmetic-failure option or the org.openjml.option.arithmetic-failure property should be one of 'hard', 'soft', or 'quiet': zzz
                1 warning
                """);
    }

    @Test
    public void testOptionArithHard() {
        helper(new String[] {"--arithmetic-failure=hard","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionArithSoft() {
        helper(new String[] {"--arithmetic-failure=soft","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionArithQuiet() {
        helper(new String[] {"--arithmetic-failure=quiet","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionArithNo() {
        helper(new String[] {"--no-arithmetic-failure=hard","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: no- is only permitted for boolean options (and --warn)
                1 warning
                """);
    }

    @Test
    public void testOptionArithNoDef() {
        helper(new String[] {"--no-arithmetic-failure=","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: no- is not permitted with set-to-default (empty string after = character)
                1 warning
                """);
    }

    @Test
    public void testOptionBV() {
        helper(new String[] {"--esc-bv=","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionBVAuto() {
        helper(new String[] {"--esc-bv=auto","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionBVTrue() {
        helper(new String[] {"--esc-bv=true","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionBVFalse() {
        helper(new String[] {"--esc-bv=false","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionBVBad() {
        helper(new String[] {"--esc-bv=zzz","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: Command-line argument error: Expected 'auto', 'true' or 'false' for --esc-bv: zzz
                1 warning
                """);
    }

    @Test
    public void testOptionWarn() {
        helper(new String[] {"--warn=zzz","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: In --(no-)warn, 'zzz' is not a valid warning key; see --help=warn
                1 warning
                """);
    }

    @Test
    public void testOptionWarnNone() {
        helper(new String[] {"--warn=","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionWarnEmpty() {
        helper(new String[] {"--warn=,","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionWarnWS() {
        helper(new String[] {"--warn= ,,\t","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: In --(no-)warn, ' ' is not a valid warning key; see --help=warn
                warning: In --(no-)warn, '' is not a valid warning key; see --help=warn
                warning: In --(no-)warn, '\t' is not a valid warning key; see --help=warn
                3 warnings
                """);
    }

    @Test
    public void testOptionWarnOK() {
        helper(new String[] {"--warn=implicit-everything","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionWarnNeg() {
        helper(new String[] {"--no-warn=implicit-everything","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionVerboseness() {
        helper(new String[] {"--verboseness=zzz","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: The value of the --verboseness option or the org.openjml.option.verboseness property should be the string representation of an integer: "zzz"
                1 warning
                """);
    }

    @Test
    public void testOptionVerbosenessDef() {
        helper(new String[] {"--verboseness=","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionVerbosenessWS() {
        helper(new String[] {"--verboseness= ","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: The value of the --verboseness option or the org.openjml.option.verboseness property should be the string representation of an integer: ""
                1 warning
                """);
    }

    @Test
    public void testOptionFeas() {
        helper(new String[] {"--check-feasibility=","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionFeasDebug() {
        helper(new String[] {"--check-feasibility=debug:x","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionRacShowSource() {
        helper(new String[] {"--rac-show-source=","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionRacShowSource1() {
        helper(new String[] {"--rac-show-source=zzz","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: Command-line argument error: Expected 'none', 'line' or 'source' for --rac-show-source : zzz
                1 warning
                """);
    }

    @Test
    public void testOptionMaxWarnings() {
        helper(new String[] {"--esc-max-warnings=zzz","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 2, 0,
                "",
                """
                error: Expected a number or 'all' as argument for --esc-max-warnings: zzz
                """);
    }

    @Test
    public void testOptionMaxWarnings0() {
        helper(new String[] {"--esc-max-warnings=0","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionMaxWarningsAll() {
        helper(new String[] {"--esc-max-warnings=all","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionMaxWarningsEmpty() {
        helper(new String[] {"--esc-max-warnings= ","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 2, 0,
                "",
                "error: Expected a number or 'all' as argument for --esc-max-warnings:  \n"
                );
    }

    @Test
    public void testOptionMaxWarningsNegative() {
        helper(new String[] {"--esc-max-warnings=-10","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionMaxWarningsPositive() {
        helper(new String[] {"--esc-max-warnings=1","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionRacShowSourceBad() {
        helper(new String[] {"--rac-show-source=zzz","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                warning: Command-line argument error: Expected 'none', 'line' or 'source' for --rac-show-source : zzz
                1 warning
                """);
    }

    @Test
    public void testOptionRacShowSourceLine() {
        helper(new String[] {"--rac-show-source=line","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionRacShowSourceNone() {
        helper(new String[] {"--rac-show-source=none","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionRacShowSourceSource() {
        helper(new String[] {"--rac-show-source=source","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionRacShowSourceWS() {
        helper(new String[] {"--rac-show-source= ","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                "warning: Command-line argument error: Expected 'none', 'line' or 'source' for --rac-show-source :  \n1 warning\n"
                );
    }

    @Test
    public void testOptionRacShowSourceDef() {
        helper(new String[] {"--rac-show-source=","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 0, 0,
                "",
                """
                """);
    }

    @Test
    public void testOptionMissingModelRep() {
        helper(new String[] {"--rac-missing-model-field-rep=zzz","-sourcepath",src + "testNoErrors",src + "testNoErrors/A.java"}, 2, 0,
                "",
                """
                error: Command-line argument error: Expected one of zero zero-quiet skip skip-quiet fail for --rac-missing-model-field-rep : zzz
                """);
    }

    @Test
    public void testModelBug2() throws Exception {
        helper(new String[]
                          { "--no-purity-check",  //"-Xlint:unchecked",
                            src+"testModelBug2/NonGenericModelClassExampleBug.java",
                            src+"testModelBug2/NonGenericModelClassExampleBugSub.java",
                          },0,0
                          ,""
                          ,""
                          );
    }

    @Test
    public void testExtension1() throws Exception {
        helper(new String[]
                { "-classpath","../OpenJML21/runtime",
                  "-sourcepath",src + "testNoErrors",
                  "--specs-path","../OpenJML21/release-temp",
                  "-lang=jml",
                  "-extensions=X", // Ignored when strict
                  src + "testNoErrors/A.java"
                },0,0
                ,""
                ,""
                );
    }

    @Test
    public void testExtension2() throws Exception {
        helper(new String[]
                { "-classpath","../OpenJML21/runtime",
                  "-sourcepath",src + "testNoErrors",
                  "-extensions=X",
                  src + "testNoErrors/A.java"
                },2,1
                ,"error: Failed to load extension X: No such package found"
                ,""
                );
    }

    @Test @Ignore // FIXME - have not yet fixed how extensions are found
    public void testExtension() throws Exception {
        helper(new String[]
                { "-classpath","../OpenJML21/runtime",
                  "-sourcepath",src + "testExtension",
                  "-extensions=ext",
                  src + "testExtension/A.java"
                },0,0
                ,""
                );
    }
    
    
    // The remaining tests are replicates of those executed by 'make release-test'
    // FIXME - check the version
    // FIXME - testOK2, testOK3, testJmlBad2
    // FIXME - test RAC-OK, SIMPLE, etc.
    
    @Test
    public void release_testJmlHelpSimp() throws Exception {
        helper(new String[]
                { 
                },2,0
                ,"Usage: openjml <options> <source files>\nUse option '-?' to list options\n"
                );
    }

    @Test
    public void release_testJmlHelpH() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "-help"
                },0,0
                ,""
                );
    }

    @Test
    public void release_testJmlHelpHH() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "--help"
                },0,0
                ,""
                );
    }

    @Test
    public void release_testJmlHelpQ() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "-?"
                },0,0
                ,""
                );
    }

    @Test
    public void release_testJmlHelpDup() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "-?","--help"
                },0,0
                ,""
                );
    }

    @Test
    public void release_testJmlBada() throws Exception {
        expectedFile = "releaseTests/testJmlBadNoSource/expected";
        helper(new String[]
                { "--verboseness="
                },2,0
                ,""
                );
    }

    @Test
    public void release_testJmlBadb() throws Exception {
        expectedFile = "releaseTests/testJmlBadWarn/expected";
        helper(new String[]
                { "--verboseness"
                },2,0
                ,""
                );
    }

    @Test
    public void release_testJmlBadc2() throws Exception {
        expectedFile = "releaseTests/testJmlBad/expected";
        helper(new String[]
                { "--verboseness", ""
                },2,0
                );
    }

    @Test
    public void release_testJmlBadd() throws Exception {
        expectedFile = "releaseTests/testJmlBad/expected";
        helper(new String[]
                { "-verboseness= "
                },2,0
                );
    }

    // FIXME - check bad verboseness property -- testJmlBad2 (2 tests)

    @Test
    public void release_testJmlBad3() throws Exception {  // FIXME - shouldn't this have error mesages
    	expectedFile = "releaseTests/testJmlBad3/expected";
    	helper(new String[]
                { "-check","-java"
                },2,0
                ,""
                );
    }
    
    @Test
    public void release_testOK1() throws Exception {
    	helper(new String[]
    			{ "--no-purity-check","--specs-path","releaseTests/testOK1","temp-release/B.java"
    			},0,0
    			,""
    			);
    }
    
    // FIXME - missing the verbose test - testOK3
    // FIXME - missing all the rac tests

    // Testing typechecking without org.jmlspecs.annotation.*
    @Test @Ignore // FIXME: Cannot currently turn off internal runtime library
    public void release_testRuntime1() throws Exception {
    	expectedFile = "releaseTests/testRuntime1/expected";
    	helper(new String[]
    			{ "temp-release/C.java", "-jmltesting", "-classpath", ".", "--no-purity-check"
    			},3,0
    			,""
    			);
    }
    
    // Testing typechecking with normal internal libraries
    @Test
    public void release_testRuntime4() throws Exception {
    	expectedFile = "releaseTests/testRuntime4/expected";
    	helper(new String[]
    			{ "temp-release/C.java", "--no-purity-check",
    			},0,0
    			,""
    			);
    }
    
    // Testing typechecking with normal internal libaries
    @Test
    public void release_testRuntime5() throws Exception {
    	expectedFile = "releaseTests/testRuntime5/expected";
    	helper(new String[]
    			{ "temp-release/D.java", "--no-purity-check",
    			},0,0
    			,""
    			);
    }
    
    @Test
    public void release_testEsc1() throws Exception {
    	expectedFile = "releaseTests/testEsc1/expected";
    	helper(new String[]
    			{ "--no-purity-check", "--esc", relsrc + "/testEsc/A.java", "-classpath", relsrc + "/testEsc"
    			},6,0
    			,""
    			);
    }
    
    @Test
    public void release_testEsc2() throws Exception {
        expectedFile = "releaseTests/testEsc2/expected";
        helper(new String[]
                { "--no-purity-check", "--esc", relsrc + "/testEsc/B.java", "-classpath", relsrc + "/testEsc"
                },0,0
                ,""
                );
    }
    
    @Test
    public void release_testEsc3() throws Exception {
        expectedFile = "releaseTests/testEsc2/expected";
        helper(new String[]
                { "--no-purity-check", "--esc", relsrc + "/testEsc/B.java", "-classpath", relsrc + "/testEsc",
                        "--exec=" + JmlTestSuite.root + "/Solvers/Solvers-macos/z3-4.3.1"
                },0,0
                ,""
                );
    }
    
    @Test
    public void release_testPath1() throws Exception {
    	expectedFile = "releaseTests/testPath1/expected";
    	helper(new String[]
    			{ "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", 
    			},1,0
    			,""
    			);
    }
    
    @Test
    public void release_testPath2() throws Exception {
    	expectedFile = "releaseTests/testPath2/expected";
    	helper(new String[]
    			{ "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data"
    			},1,1
    			,""
    			);
    }
    
    @Test
    public void release_testPath3() throws Exception {
    	expectedFile = "releaseTests/testPath3/expected";
    	helper(new String[]
    			{ "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "--specs-path", relsrc + "/testPath/data-specs"
    			},1,1
    			,""
    			);
    }
    
    @Test
    public void release_testPath4() throws Exception {
        expectedFile = "releaseTests/testPath4/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data-specs" 
                },1,0
                ,""
                );
    }
    
    @Test
    public void release_testPath5() throws Exception {
        expectedFile = "releaseTests/testPath5/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data-specs" + z + relsrc + "/testPath/data" 
                },1,0
                ,""
                );
    }
    
    @Test
    public void release_testPath6() throws Exception {
        expectedFile = "releaseTests/testPath6/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data" + z + relsrc + "/testPath/data-specs" 
                },1,0
                ,""
                );
    }
    
    @Test
    public void release_testPath7() throws Exception {
        expectedFile = "releaseTests/testPath7/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data", "--specs-path", relsrc + "/testPath/data-specs" 
                },1,0
                ,""
                );
    }
    
    @Test
    public void release_testPath8() throws Exception {
        expectedFile = "releaseTests/testPath8/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data-specs" + z + relsrc + "/testPath/data"
                },1,0
                ,""
                );
    }
    
    @Test
    public void release_testPath9() throws Exception {
        expectedFile = "releaseTests/testPath9/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data:" + relsrc + "/testPath/data-specs"
                },1,0
                ,""
                );
    }
    
    @Test
    public void release_testPath10() throws Exception {
        expectedFile = "releaseTests/testPath10/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data", "--specs-path", relsrc + "/testPath/data-specs"
                },1,0
                ,""
                );
    }
    
    @Test
    public void release_testCheck1() throws Exception {
        expectedFile = "releaseTests/testCheck1/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", "--specs-path", relsrc, relsrc + "/A.java"
                },1,0
                ,""
                );
    }
    
    // FIXME - testAPI
    // FIXME - jmldoc and prettyprinting

}
