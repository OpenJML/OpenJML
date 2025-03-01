package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assume;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check running ESC on files in the file system, comparing the
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
@RunWith(ParameterizedWithNames.class)
public class escfiles2 extends EscBaseFiles {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    @Test
    public void gitbug362() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug450a() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug450b() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void gitbug455a() {
        helpTCG();
    }
    
    @Test
    public void gitbug600() {
        helpTCG();
    }
    
    @Test @Ignore // FIXME - times out in attempting to prove
    public void gitbug802() {
        helpTCG();
    }
    
    @Test
    public void importProblem() {
        helpTCG();
    }
    
    @Test
    public void importProblem2() {
        helpTCG();
    }
    
    @Test
    public void imports() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void recommends() {
        helpTCG("--show=program","--code-math=bigint");
    }
    
    @Test
    public void recommendsA() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void recommendsB() {
        expectedExit = 1;
        helpTCG();
    }
    
    @Test
    public void recommendsC() {
        helpTCG();
    }
    
    @Test
    public void escRawding2() {
        helpTCG();
    }
    
    @Test
    public void escRawdingA() {
        helpTCG();
    }
    
    @Test
    public void escRawdingB() {
        helpTCG();
    }
    
    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
        //Assert.fail(); // FIXME - Java8 - long running
        ArrayList<String> list = new ArrayList<String>();
        list.add("-code-math=safe");
        list.add("-spec-math=bigint");
        list.add("--check-feasibility=precondition,reachable,exit,spec");
        list.add("--progress");
        list.addAll(Arrays.asList(opts));
        escOnFiles(sourceDirname,outDir,list.toArray(opts));
    }
    
    @Test public void typecheckWithJML() {
        expectedExit = 1;
        helpTCF("test/tcWithJml/TCWithJml.java","test/tcWithJml", "-cp", "test/tcWithJml", "--check");
    }
    
    @Test public void sfpatch25() {
        helpTCF("test/sfpatch25/A.java","test/sfpatch25", "-cp", "test/sfpatch25", "--esc","--quiet");
    }
    
    @Test public void sfbug407() {
        helpTCF("test/sfbug407","test/sfbug407", "-cp", "test/sfbug407", "--esc", "--progress");
    }
    
    @Test public void sfbug398() {
        helpTCF("test/sfbug398","test/sfbug398", "-cp", "test/sfbug398", "--esc", "--progress");
    }
    
    @Test public void sfbug399() {
        helpTCF("test/sfbug399","test/sfbug399", "-cp", "test/sfbug399", "--esc","--progress");
    }
    
    @Test public void sfbug404() {
        helpTCF("test/sfbug404","test/sfbug404", "-cp", "test/sfbug404", "--esc","--progress","-logic=AUFNIRA");
    }
    
    @Test public void sfbug408() {
        helpTCF("test/sfbug408","test/sfbug408", "-cp", "test/sfbug408", "--esc","--progress");
    }
    
    @Test public void sfbug409() {
        helpTCF("test/sfbug409","test/sfbug409", "-cp", "test/sfbug409", "--esc","--progress","--check-feasibility=precondition,exit,reachable,assert,assume");
    }
    
    @Test public void sfbug410() {
        helpTCF("test/sfbug410","test/sfbug410", "-cp", "test/sfbug410", "--esc","--progress");
    }
    



}
