package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RunBase;

import java.io.File;

import org.junit.*;

/** Each test in this suite runs a teset that is a (bash) script. The testName is the name of the
 * test method. The script that is run is '.../OpenJMLTest/test/NAME/run', where NAME is the test name.
 * The script is expected to end with an exit code of 0 if it is successful and something non-zero otherwise.
 * In normal (non-debug) operation, a successful exit should emit no other output (on System.out or System.err)
 * and should leave behind no temporary files;/ it should be robust against the left over presence of any files.
 * The test scripts should do their own comparisons of actual output vs. expected output, where the expected output
 * is contained in files typically named 'expected' (in the same folder as 'run'); 
 * if the output does not match the contents of 'expected', then the actual output should be preserved in a file named 'actual'.
 */
public class runscripts2 extends RunBase {
    
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

    @Test public void apiAST() {
        doTest();
    }

    @Test public void apiASTCrash() {
        doTest();
    }

    @Test public void findSpecs() {
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
    
    @Test public void inferoptions() {
        doTest();
    }
    
    @Test public void warningoptions() {
        doTest();
    }
}
