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

/** This file contains RAC tests of the JML value types. The files referenced are also used for ESC tests in primesc. */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class primrac extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        setUpForFiles();
        super.setUp();
        ignoreNotes = true;
    }
    
    @Test
    public void jmlTYPE() {
        helpCompileRun("Test");
    }

    @Test
    public void jmlreal() {
        helpCompileRun("Test");
    }

    @Test
    public void jmlbigint() {
        helpCompileRun("Test");
    }

    @Test
    public void jmlrange() {
        expectedExit = 0;
        helpCompileRun("TestRange");
    }
    
    @Test
    public void jmlstring() {
        expectedExit = 0;
        helpCompileRun("TString");
    }
    
    @Test
    public void jmlseq() {
        expectedExit = 0;
        helpCompileRun("TSeq");
    }
    
    @Test
    public void jmlarray() {
        expectedExit = 0;
        helpCompileRun("Tarray");
    }
    
    @Test
    public void jmlset() {
        expectedExit = 0;
        helpCompileRun("TSet");
    }
    
    @Test
    public void jmlmap() {
        expectedExit = 1;
        helpCompileRun("Tmap");
    }
    
    // TODO: Review the remainder of these and incorporate them in the above as appropriate.
    
    @Test
    public void racbigint() { // FIXME - do these duplicate
        expectedExit = 0;
        helpTCF("test/racbigint","test/racbigint","bigint");
    }

    @Test
    public void racreal() {  // FIXME - do these duplicate
        expectedExit = 0;
        helpTCF("test/racreal","test/racreal","real");
    }
    
    
    @Test 
    public void valuestrings() {
        expectedRACExit = 0;
        helpTCF("test/valuestrings","test/valuestrings","JMLStringTest");
    }

    @Test
    public void rangeTest() {
        helpCompileRun("test/rangeTest","test/rangeTest","R");
    }
    
    @Test
    public void rangeTest1() {
        expectedExit=1;
        helpCompileOnly();
    }
    


}
