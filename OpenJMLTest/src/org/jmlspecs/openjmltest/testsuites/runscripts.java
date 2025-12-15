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
public class runscripts extends RunBase {
    
    @Test public void sourcepath() {
        doTest();
    }

    @Test public void specspath() {
        doTest();
    }

    @Test public void apiZ() {
        doTest();
    }

    @Test public void apiA() {
        doTest();
    }

    @Test public void apiB() {
        doTest();
    }

    @Test public void apiC() {
        doTest();
    }

    @Test public void apiD() {
        doTest();
    }

    @Test public void apiE() {
        doTest();
    }

    @Test public void apiOut() {
        doTest();
    }

    @Test public void apiToken() {
        doTest();
    }

    @Test public void apiinstance() {
        doTest();
    }

    @Test public void findSpecs() {
        doTest();
    }

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

    @Test public void scandebug() {
        doTest();
    }

    @Test public void showSkipped() {
        doTest();
    }

    @Test public void requireWhitespace() {
        doTest();
    }

    @Test public void optionJml() {
        doTest();
    }

    @Test public void properties() {
        doTest();
    }

    @Test public void nowarn() {
        doTest();
    }
    
    @Test public void warningoptions() {
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
    
    @Test public void runscriptTimeout() {
        try {
            timeoutMS=1000;
            doTest();
        } catch (AssertionError e) {
            org.junit.Assert.assertEquals("unexpected output", 
                    "Test runscriptTimeout: did not complete within the timeout period",
                    e.getMessage());
        }
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
            var suite = "org.jmlspecs.openjmltest.testsuites.runscripts";
            {
                var runsuite = Class.forName(suite);
                var runmethods = java.util.Arrays.stream(runsuite.getDeclaredMethods()).filter(method->method.getAnnotationsByType(org.junit.Test.class).length != 0)
                    .map(m->m.getName()).collect(java.util.stream.Collectors.toList());
                allfiles.removeAll(runmethods);
            }
            if (allfiles.size() != 0) {
                System.out.println("ORPHANED RUN TESTS: " + allfiles);
            }
            Assert.assertEquals("ORPHANED RUN TESTS: " + allfiles, allfiles.size(), 0);
        } catch (Exception e) {
            throw new AssertionError("Exception while determining test methods in racfileslist: " + e);
        }

    }
}
