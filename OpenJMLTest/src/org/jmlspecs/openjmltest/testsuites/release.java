package org.jmlspecs.openjmltest.testsuites;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
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


// FIXME - the helper methods here are duplicates of those in compiler

// FIXME - missing testAPI
// FIXME - missing the verbose test - testOK3
// FIXME - missing all the rac tests


/** Tests that replicate the release tests, except that the release tests are run as scripts
 * and they are duplicated here by invoking the OpenJML api (calling o-enjml through 
 * org.jmlspecs.openjml.Main.execute */

// In these tests, all the expected output is in external files -- the same files as are used by the 
// release tests themselves.
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class release extends JmlTestSuite {

    public static final String relsrc = "releaseTests/src";
    public static final String src = "test/compiler/";

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
        // Do this just in case the test fails without having reset the streams
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
        if (expectedFile == null && expectedOutput == null) {
            fail("No expected file or output set");
            return; // Just to convince java that this branch does not continue
        } else {
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

    // The remaining tests are replicates of those executed by 'make release-test'
    // FIXME - check the version
    // FIXME - testOK2, testOK3, testJmlBad2
    // FIXME - test RAC-OK, SIMPLE, etc.

    @Test
    public void release_testJmlHelpSimp() throws Exception {
        expectedOutput = "Usage: openjml <options> <source files>\nUse option '-?' to list options\n";
        helper(new String[]
                { 
                },2
                );
    }

    @Test
    public void release_testJmlHelpH() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "-help"
                },0
                );
    }

    @Test
    public void release_testJmlHelpHH() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "--help"
                },0
                );
    }

    @Test
    public void release_testJmlHelpQ() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "-?"
                },0
                );
    }

    @Test
    public void release_testJmlHelpDup() throws Exception {
        expectedFile = "releaseTests/testJmlHelp/expected";
        helper(new String[]
                { "-?","--help"
                },0
                );
    }

    @Test
    public void release_testJmlBadNoSource() throws Exception {
        expectedFile = "releaseTests/testJmlBadNoSource/expected";
        helper(new String[]
                { "--verboseness="
                },2
                );
    }

    @Test
    public void release_testJmlBadNoValue() throws Exception {
        expectedFile = "releaseTests/testJmlBadWarn/expected";
        helper(new String[]
                { "--verboseness"
                },2
                );
    }

    @Test
    public void release_testJmlBadEmpty() throws Exception {
        expectedFile = "releaseTests/testJmlBad/expected";
        helper(new String[]
                { "--verboseness", ""
                },2
                );
    }

    @Test
    public void release_testJmlBadNoSourceWS() throws Exception {
        expectedFile = "releaseTests/testJmlBad/expected";
        helper(new String[]
                { "--verboseness= "
                },2
                );
    }

    @Test
    public void release_testJmlBadNoSourceWS2() throws Exception {
        expectedFile = "releaseTests/testJmlBad/expected";
        helper(new String[]
                { "-verboseness= "
                },2
                );
    }

    // FIXME - check bad verboseness property -- testJmlBadProperty (2 tests)

    @Test
    public void release_testJmlBadJava() throws Exception {  // FIXME - shouldn't this have error mesages
        expectedFile = "releaseTests/testJmlBad3/expected";
        helper(new String[]
                { "-check","-java"
                },2
                );
    }

    @Test
    public void release_testOK1() throws Exception {
        expectedOutput = "";
        helper(new String[]
                { "--no-purity-check","--specs-path","releaseTests/testOK1","temp-release/B.java"
                },0
                );
    }

    // Testing typechecking with normal internal libraries
    @Test
    public void release_testRuntime4() throws Exception {
        expectedFile = "releaseTests/testRuntime4/expected";
        helper(new String[]
                { "temp-release/C.java", "--no-purity-check",
                },0
                );
    }

    // Testing typechecking with normal internal libaries
    @Test
    public void release_testRuntime5() throws Exception {
        expectedFile = "releaseTests/testRuntime5/expected";
        helper(new String[]
                { "temp-release/D.java", "--no-purity-check",
                },0
                );
    }

    @Test
    public void release_testEsc1() throws Exception {
        expectedFile = "releaseTests/testEsc1/expected";
        helper(new String[]
                { "--no-purity-check", "--esc", relsrc + "/testEsc/A.java", "-classpath", relsrc + "/testEsc"
                },6
                );
    }

    @Test
    public void release_testEsc2() throws Exception {
        expectedFile = "releaseTests/testEsc2/expected";
        helper(new String[]
                { "--no-purity-check", "--esc", relsrc + "/testEsc/B.java", "-classpath", relsrc + "/testEsc"
                },0
                );
    }

    @Test
    public void release_testEsc3() throws Exception {
        expectedFile = "releaseTests/testEsc2/expected";
        helper(new String[]
                { "--no-purity-check", "--esc", relsrc + "/testEsc/B.java", "-classpath", relsrc + "/testEsc",
                        "--exec=" + JmlTestSuite.root + "/Solvers/Solvers-macos/z3-4.3.1"
                },0
                );
    }

    @Test
    public void release_testPath1() throws Exception {
        expectedFile = "releaseTests/testPath1/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", 
                },1
                );
    }

    @Test
    public void release_testPath2() throws Exception {
        expectedFile = "releaseTests/testPath2/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data"
                },1
                );
    }

    @Test
    public void release_testPath3() throws Exception {
        expectedFile = "releaseTests/testPath3/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "--specs-path", relsrc + "/testPath/data-specs"
                },1
                );
    }

    @Test
    public void release_testPath4() throws Exception {
        expectedFile = "releaseTests/testPath4/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data-specs" 
                },1
                );
    }

    @Test
    public void release_testPath5() throws Exception {
        expectedFile = "releaseTests/testPath5/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data-specs" + z + relsrc + "/testPath/data" 
                },1
                );
    }

    @Test
    public void release_testPath6() throws Exception {
        expectedFile = "releaseTests/testPath6/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data" + z + relsrc + "/testPath/data-specs" 
                },1
                );
    }

    @Test
    public void release_testPath7() throws Exception {
        expectedFile = "releaseTests/testPath7/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-sourcepath", relsrc + "/testPath/data", "--specs-path", relsrc + "/testPath/data-specs" 
                },1
                );
    }

    @Test
    public void release_testPath8() throws Exception {
        expectedFile = "releaseTests/testPath8/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data-specs" + z + relsrc + "/testPath/data"
                },1
                );
    }

    @Test
    public void release_testPath9() throws Exception {
        expectedFile = "releaseTests/testPath9/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data:" + relsrc + "/testPath/data-specs"
                },1
                );
    }

    @Test
    public void release_testPath10() throws Exception {
        expectedFile = "releaseTests/testPath10/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", relsrc + "/testPath/data/TestPath.java", "-classpath", relsrc + "/testPath/data", "--specs-path", relsrc + "/testPath/data-specs"
                },1
                );
    }

    @Test
    public void release_testCheck1() throws Exception {
        expectedFile = "releaseTests/testCheck1/expected";
        helper(new String[]
                { "-jmltesting", "--no-purity-check", "--specs-path", relsrc, relsrc + "/A.java"
                },1
                );
    }

}
