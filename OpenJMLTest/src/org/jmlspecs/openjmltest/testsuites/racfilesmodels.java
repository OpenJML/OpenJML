package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

/** These tests check running RAC on files in the file system, comparing the
 * output against expected files. These tests are a bit easier to create, since 
 * the file and output do not have to be converted into Strings; however, they
 * are not as easily read, since the content is tucked away in files, rather 
 * than immediately there in the test class.
 * <P>
 * To add a new test:
 * <UL>
 * <LI> create a directory containing the test files as a subdirectory of 
 * 'test'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racfilesmodels extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        setUpForFiles();
        super.setUp();
        ignoreNotes = true;
    }

    @Test @Ignore // model files
    public void gitbug524() {
        expectedRACExit = 0;
        helpTCF("test/gitbug524","test/gitbug524","Test"); 
    }

    @Test @Ignore // model files
    public void gitbug584() {
        helpTCF("test/gitbug584","test/gitbug584","AClass");
    }

    @Test @Ignore // model files
    public void gitbug590() {
        runrac = false; // Expected compile error
        expectedExit = 1;
        helpTCF("test/gitbug590","test/gitbug590","Sequence");
    }

    @Test @Ignore // model files
    public void gitbug590a() {
        runrac = true;
        expectedRACExit = 0;
        expectedExit = 0;
        helpTCF("test/gitbug590a","test/gitbug590a","Sequence");
    }

}
