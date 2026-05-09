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
        super.setUp();
    }
    
    @Test
    public void jmlTYPE() {
        helpCompileRun("Test","--rac-java-checks");
    }

    @Test
    public void jmlreal() {
        helpCompileRun("Treal");
    }

    @Test
    public void jmlbigint() {
        helpCompileRun("Tbigint");
    }

    @Test
    public void jmldatagroup() {
        expectedExit = 0;
        helpCompileRun("Tdatagroup");
    }
    
    @Test
    public void jmlrange() {
        expectedExit = 0;
        helpCompileRun("Trange");
    }
    
    @Test
    public void jmlstring() {
        expectedExit = 0;
        helpCompileRun("TString");
    }
    
    @Test
    public void jmlstring2() {
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
        expectedExit = 0;
        helpCompileRun("Tmap");
    }
    
    @Test
    public void jmlinit() {
        expectedExit = 0;
        helpCompileRun("Tinit");
    }
    
    // TODO: Review the remainder of these and incorporate them in the above as appropriate.
    
    @Test
    public void racbigint() { // FIXME - do these duplicate
        expectedExit = 0;
        helpCompileRun("bigint");
    }

    @Test
    public void racreal() {  // FIXME - do these duplicate
        expectedExit = 0;
        helpCompileRun("real");
    }
    
    
    @Test 
    public void valuestrings() {
        expectedRACExit = 0;
        helpCompileRun("JMLStringTest");
    }
}
