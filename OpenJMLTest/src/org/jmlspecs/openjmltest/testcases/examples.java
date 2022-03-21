package org.jmlspecs.openjmltest.testcases;

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
import org.jmlspecs.openjmltest.EscBase;
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
public class examples extends EscBase {

    boolean enableSubexpressions = false;
    
    public examples(String options, String solver) {
        super(options,solver);
    }
    
    // These paths are relative to OpenJML/OpenJMLTest in a standard development environment
    String inPath = "../../openjml.github.io/examples/";
    String outPath = "test-results/";
    
    
    String[] rac = null;
    
    /** The command-line to use to run ESC on a program */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
        super.setUp();
    	ignoreNotes = true;
    }
    
    public void helpDemo(String testFileName, String ... opts) {
        int extraopts = 3;
        String[] newopts = new String[opts.length+extraopts];
        newopts[0] = "-classpath";
        newopts[1] = inPath;
        newopts[2] = "-code-math=safe"; // FIXME - omit this when EscBase does not set code-math
        System.arraycopy(opts,0,newopts,extraopts,opts.length);
        helpTCF(inPath + testFileName, outPath + testFileName.substring(0,testFileName.indexOf('.')),newopts);
    }

    public void helpTCF(String demoFile, String outDir, String ... opts) {
        escOnFiles(demoFile,outDir,opts);
    }
    
    // Files to skip in the general loop, perhaps because they run long
    final String[] skip = new String[] { "Challenge1A2019.java", "Challenge2A2019.java" };

    // Runs through all the .java files in 'inPath', testing each one against the expected output in outPath/classname
    // Note that this test is limited by the overall time limit on an individual JUnit test, so it can't run too many tests
    @Test
    public void testAll() {
        boolean failed = false;
        int tests = 0;
        // Note that File.list does not guarantee any order
        for (String f: new File(inPath).list((File d, String s)->s.endsWith(".java") && !Arrays.stream(skip).anyMatch(ss->ss.equals(s)))) {
            System.out.println("Checking " + f);
            try {
                helpDemo(f);
                tests++;
            } catch (Throwable t) {
                failed = true;
            }
        }
        System.out.println(tests + " successes");
        if (failed) fail();
    }

    // Use this form for individual tests by name
    @Test
    public void testChallenge1A2019() {
        helpDemo("Challenge1A2019.java");
    }

    @Test
    public void testChallenge2A2019() {
        helpDemo("Challenge2A2019.java");
    }



}
