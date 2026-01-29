package org.jmlspecs.openjmltest.testsuites;

import java.io.File;

import org.jmlspecs.openjmltest.*;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.Assert;

/** Each test in this suite runs a teset that is a (bash) script. The testName is the name of the
 * test method. The script that is run is '.../OpenJMLTest/test/NAME/run', where NAME is the test name.
 * The script is expected to end with an exit code of 0 if it is successful and something non-zero otherwise.
 * In normal (non-debug) operation, a successful exit should emit no other output (on System.out or System.err)
 * and should leave behind no temporary files;/ it should be robust against the left over presence of any files.
 * The test scripts should do their own comparisons of actual output vs. expected output, where the expected output
 * is contained in files typically named 'expected' (in the same folder as 'run'); 
 * if the output does not match the contents of 'expected', then the actual output should be preserved in a file named 'actual'.
 */
public class runscripts1 extends RunBase {
    
    @Test public void gitbug449() {
        doTest();
    }
    
    @Test public void gitbug546() {
        doTest();
    }
    
    @Test public void gitbug752() {
        doTest();
    }

    @Test public void gitbug776() {
        doTest();
    }

    @Test public void gitbug784() {
        doTest();
    }

    @Test public void gitbug786() {
        doTest();
    }

    @Test public void gitbug786a() {
        doTest();
    }

    // gitbug857
    @Test public void crashXlint() {
        doTest();
    }

    @Test public void javaonly() {
        doTest();
    }

    @Test public void nomodelfield() {
        doTest();
    }

    @Test public void nomodelmethod() {
        doTest();
    }

    @Test public void prefer1() {
        doTest();
    }

    
    @Test public void quiet() {
        doTest();
    }
    
    @Test public void unicodeErrors() {
        doTest();
    }
    
    // The next few tests are harness tests: intentional errors to check whether the test harness code correctly reports those errors
    
    @Test public void noSuchTestFolder() {
        try {
            doTest();
        } catch (AssertionError e) {
            org.junit.Assert.assertEquals("unexpected output", 
                "Test noSuchTestFolder: failed to launch or to execute: java.io.IOException: Cannot run program \"./run\" (in directory \"test/noSuchTestFolder\"): error=2, No such file or directory",
                e.getMessage());
        }
    }
    
    // The JUnit 4 timeout option on the Test annotation does not work here -- FIXME - because the OpenJMLTestRunner does not read it
    @Test public void runscriptTimeout() {
        try {
            timeoutMS=1000;
            doTest();
            org.junit.Assert.fail("Did not timeout");
        } catch (AssertionError e) {
            org.junit.Assert.assertEquals("unexpected output", 
                    "Test runscriptTimeout: did not complete within the timeout period",
                    e.getMessage());
        }
    }
    
    @Test public void runscriptTimeoutOK() {
        timeoutMS=100000;
        doTest();
    }
    
    @Test public void runscriptBadExit() {
        try {
            doTest();
        } catch (AssertionError e) {
            org.junit.Assert.assertEquals("unexpected output", 
                    "Test runscriptBadExit: emitted a failure exit code: expected:<0> but was:<2>",
                    e.getMessage());
        }
    }
    
    // If this test fails, then there are some script-style tests (that is, folders containing a 'run' script) that are not listed as
    // individual methods above
    @Test public void anyOrphanedTests() {
        try {
            java.util.SortedSet<String> allfiles = new java.util.TreeSet<String>();
            var dir = new File("test");
            for (var f: dir.listFiles()) {
                if (new java.io.File(f, "run").exists()) {
                    allfiles.add(f.getName());
                }
            }
            {
                var suite = "org.jmlspecs.openjmltest.testsuites.runscripts1";
                var runsuite = Class.forName(suite);
                var runmethods = java.util.Arrays.stream(runsuite.getDeclaredMethods()).filter(method->method.getAnnotationsByType(org.junit.Test.class).length != 0)
                    .map(m->m.getName()).collect(java.util.stream.Collectors.toList());
                allfiles.removeAll(runmethods);
            }
            {
                var suite = "org.jmlspecs.openjmltest.testsuites.runscripts2";
                var runsuite = Class.forName(suite);
                var runmethods = java.util.Arrays.stream(runsuite.getDeclaredMethods()).filter(method->method.getAnnotationsByType(org.junit.Test.class).length != 0)
                    .map(m->m.getName()).collect(java.util.stream.Collectors.toList());
                allfiles.removeAll(runmethods);
            }
            Assert.assertEquals("ORPHANED RUN TESTS: " + allfiles, 0, allfiles.size());
        } catch (Exception e) { // Internal bug or configuration error -- should not happen for any successful or failing test
            Assert.fail("Exception while determining test methods in racfileslist: " + e);
        }
    }
    
    /** This test creates an orphan test (a folder with a run script that does not have an explicit test in this suite),
     * checks that the anyOrphanedTests method detects the orphan test (and fails),
     * and then deletes the temporary orphan test
     */
    @Test public void checkOrphanedTests() {
        String nm = "test/checkOrphanedTestsTemp";
        String run = nm+"/run";
        try {
            new java.io.File(nm).mkdir();
            new java.io.File(run).createNewFile();
            anyOrphanedTests();
            Assert.fail("Failure in checkOrphanedTests"); // Internal bug or configuration error -- should not happen for any successful or failing test
        } catch (AssertionError e) {
            Assert.assertEquals("unexpected output", "ORPHANED RUN TESTS: [checkOrphanedTestsTemp] expected:<0> but was:<1>", e.getMessage());
        } catch (Exception e) { // Internal bug or configuration error -- should not happen for any successful or failing test
            Assert.fail("Exception in checkOrphanedTests: " + e);
        } finally {
            new java.io.File(run).delete();
            new java.io.File(nm).delete();
        }
    }
}
