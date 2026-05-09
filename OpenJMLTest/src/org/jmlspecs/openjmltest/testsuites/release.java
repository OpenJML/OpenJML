package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.JmlTestSuite;

import static org.junit.Assert.*;
import org.junit.*;
import org.junit.rules.TestName;


// FIXME - missing testAPI
// FIXME - missing the verbose test - testOK3
// FIXME - missing all the rac tests
// FIXME - missing property tests


/** Tests that replicate the release tests, except that the release tests are run as scripts
 * and they are duplicated here by invoking the OpenJML api (calling o-enjml through 
 * org.jmlspecs.openjml.Main.execute */

// In these tests, all the expected output is in external files -- the same files as are used by the 
// release tests themselves.
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class release extends JmlTestSuite {

    public static final String relsrc = "releaseTests/src";

    @Rule
    public TestName name = new TestName();

    boolean capture = true; // Set to false just for debugging
    String expectedFile = null;
    String expectedOutput = null;

    @Before
    public void setUp() throws Exception {
        // Purposely do not execute JmlTestSuite.setup
        //capture = false; print = true;
        if (capture) collectSystemOutput(true); // Needs to be called 
    }

    @After
    public void tearDown() {
    }

    /** This is a helper method that runs the compiler on the given set of
     * command-line arguments, checking the result
     * @param args the command-line arguments
     * @param expectedExitCode the expected exit code (0=OK, 1=completed with error messages
     *      2=command-line problems, 3=system errors, 4=abort)
     * Expects no error output; expects the std output to match either the contents of the file expectedFile
     * or the string expecteOutput.
     */
    public void helper(String[] args, int expectedExitCode) {
        print = false; // Set to true to see some debugging output
        int exitCode = 4;
        try {
            exitCode = org.jmlspecs.openjml.Main.execute(args);
        } finally {
            if (capture) collectSystemOutput(false);
        }
        // Depending on how the log is setup, error output can go to either bout or berr
        String actualOutput = output();
        String errOutput = errorOutput();

        String expected;
        String expectedErr = "";
        if (expectedOutput != null) {
            // continue
        } else if (expectedFile == null) {
            expectedFile = "releaseTests/" + getTestName() + "/expected";
        } else {
            
        }
        try {
            if (expectedOutput != null) {
                expected = expectedOutput;
            } else {
                expected = new String(java.nio.file.Files.readAllBytes(java.nio.file.Paths.get(expectedFile)));
            }
            expected = expected.replace("./src",relsrc);
            expected = JmlTestSuite.doReplacements(expected);
        } catch (Exception ee) {
            expected = null;
            fail(ee.toString());
        }
        
        actualOutput = actualOutput.replace("\r", "");
        errOutput = errOutput.replace("\r", "");
        expected = expected.replace("\r", "");

        if (print) this.out.println("EXPECTING: " + expected);
        if (print) this.out.println("ACTUAL OUT: " + actualOutput);
        if (print) this.out.println("ACTUAL ERR: " + errOutput);
        if (capture) try {
            if (print) this.out.println("TEST: " + getTestName() + " exit=" + exitCode + eol + errOutput);
            assertEquals("The output is unexpected",expected,actualOutput);
            assertEquals("The exit code is wrong",expectedExitCode,exitCode);
            assertTrue("Expected no error output", errOutput.length() == 0);
        } catch (AssertionError ex) {
            if (!print) {
                this.out.println("TEST: " + getTestName() + " exit=" + exitCode + eol + errOutput);
                this.out.println("ACTUAL OUT: " + actualOutput);
                this.out.println("ACTUAL ERR: " + errOutput);
            }
            throw ex;
        }
    }

    // These tests are replicates of those executed by 'make release-test'
    // FIXME - check the version
    // FIXME - testOK2, testOK3, testJmlBad2
    // FIXME - test RAC-OK, SIMPLE, etc.
    
    
    @Test
    public void testJmlHelpSimp() throws Exception {
        expectedOutput = "Usage: openjml <options> <source files>\nUse option '-?' to list options\n";
        helper(new String[]
                { 
                },2
                );
    }

    @Test
    public void testJmlHelpQ() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "-?"
                },0
                );
    }

    @Test
    public void testJmlHelpHH() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "--help"
                },0
                );
    }

    @Test
    public void testJmlHelpH() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "-help"
                },0
                );
    }

    // FIXME - this is an extra test
    @Test
    public void testJmlHelpDup() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "-?","--help"
                },0
                );
    }

    @Test
    public void testJmlDefaultNoSource() throws Exception {
        expectedFile = "releaseTests/testJmlBadNoSource/expected";
        helper(new String[]
                { "--verboseness="
                },2
                );
    }

    @Test
    public void testJmlBadNoValue() throws Exception {
        helper(new String[]
                { "--verboseness"
                },2
                );
    }

    @Test
    public void testJmlBadArg() throws Exception {
        expectedFile = "releaseTests/testJmlBadArg/expected";
        helper(new String[]
                { "--verboseness", ""
                },2
                );
    }

    @Test
    public void testJmlBadArg2() throws Exception {
        expectedFile = "releaseTests/testJmlBadArg/expected";
        helper(new String[]
                { "--verboseness= "
                },2
                );
    }

// FIXME - check bad verboseness property -- testJmlBadProperty (2 tests)

    @Test
    public void testJmlBadJava() throws Exception {
        helper(new String[]
                { "-check","-java"
                },2
                );
    }

    @Test
    public void testOK1() throws Exception {
        expectedOutput = "";
        helper(new String[]
                { "--specs-path","releaseTests/testOK1","temp-release/B.java"
                },0
                );
    }

    // FIXME - rac tests

    @Test
    public void testEsc1() throws Exception {
        helper(new String[]
                {  "--esc", relsrc + "/testEsc/A.java", "-classpath", relsrc + "/testEsc"
                },6
                );
    }

    @Test
    public void testEsc2A() throws Exception {
        expectedFile = "releaseTests/testEsc2/expected";
        helper(new String[]
                { "--esc", relsrc + "/testEsc/B.java", "-classpath", relsrc + "/testEsc"
                },0
                );
    }

    @Test
    public void testEsc2B() throws Exception {
        expectedFile = "releaseTests/testEsc2/expected";
        helper(new String[]
                { "--esc", relsrc + "/testEsc/B.java", "-classpath", relsrc + "/testEsc",
                        "--exec=" + JmlTestSuite.root + "/Solvers/Solvers-macos/z3-4.3.1"
                },0
                );
    }

    @Test
    public void testPath1() throws Exception {
        helper(new String[]
                { "-jmltesting", relsrc + "/testPath/data/TestPath.java", 
                },1
                );
    }

    @Test
    public void testPath2() throws Exception {
        helper(new String[]
                { "-jmltesting", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data"
                },1
                );
    }

    @Test
    public void testPath3() throws Exception {
        helper(new String[]
                { "-jmltesting", relsrc + "/testPath/data/TestPath.java", "--specs-path", relsrc + "/testPath/data-specs"
                },1
                );
    }

    @Test
    public void testPath4() throws Exception {
        helper(new String[]
                { "-jmltesting", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data-specs" 
                },1
                );
    }

    @Test
    public void testPath5() throws Exception {
        helper(new String[]
                { "-jmltesting", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data-specs" + z + relsrc + "/testPath/data" 
                },1
                );
    }

    @Test
    public void testPath6() throws Exception {
        helper(new String[]
                { "-jmltesting", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data" + z + relsrc + "/testPath/data-specs" 
                },1
                );
    }

    @Test
    public void testPath7() throws Exception {
        helper(new String[]
                { "-jmltesting", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data", "--specs-path", relsrc + "/testPath/data-specs" 
                },1
                );
    }

    @Test
    public void testPath8() throws Exception {
        helper(new String[]
                { "-jmltesting", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data-specs" + z + relsrc + "/testPath/data"
                },1
                );
    }

    @Test
    public void testPath9() throws Exception {
        helper(new String[]
                { "-jmltesting", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data:" + relsrc + "/testPath/data-specs"
                },1
                );
    }

    @Test
    public void testPath10() throws Exception {
        helper(new String[]
                { "-jmltesting", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data", "--specs-path", relsrc + "/testPath/data-specs"
                },1
                );
    }

    @Test
    public void testCheck1() throws Exception {
        helper(new String[]
                { "-jmltesting", "--specs-path", relsrc, relsrc + "/A.java"
                },1
                );
    }

    // FIXME - missing testAPI
    
    // FIXME - these are extra
    
    // Testing typechecking with normal internal libraries
    @Test
    public void testRuntime4() throws Exception {
        helper(new String[]
                { "temp-release/C.java",
                },0
                );
    }

    // Testing typechecking with normal internal libaries
    @Test
    public void testRuntime5() throws Exception {
        helper(new String[]
                { "temp-release/D.java",
                },0
                );
    }

}
