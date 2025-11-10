package org.jmlspecs.openjmltest.testsuites;

import java.io.File;

import org.jmlspecs.openjmltest.*;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.Assert;

public class runscripts extends RunBase {
    
    @Test public void sourcepath() {
        doTest();
    }

    @Test public void specspath() {
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

    @Test public void gitbug786() {
        doTest();
    }

    @Test public void gitbug786a() {
        doTest();
    }

    @Test public void gitbug883() {
        doTest();
    }
    
    // gitbug857
    @Test public void crashXlint() {
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
    
    // If this test fails, then there are some script-style tests (that is, tests with a 'run' script) that are not listed as
    // individual methods such as those methods above
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
