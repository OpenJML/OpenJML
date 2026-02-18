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
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.*;

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
public class escfeatures extends EscBaseFiles {

    boolean enableSubexpressions = false;
    
    String[] rac = null;
    
    /** The command-line to use to run ESC on a program */
    String[] sysrac = new String[]{jdk, "-classpath","bin"+z+"../OpenJML/bin-runtime",null};

    @Override
    public void setUp() throws Exception {
        rac = sysrac;
        super.setUp();
        ignoreNotes = true;
    }
    
    public void helpFeatures() {
        expectedExit = 6;
        String n = getTestName();
        helpEscFile(OpenJMLDemoPath + "/src/features/"+n+".java","test/features/"+n,"--check-feasibility=basic","--progress","--verify-exit=6");
    }


    @Test
    public void IndexOutOfRange() {
        helpFeatures();
    }

    @Test
    public void IllegalArgument() {
        helpFeatures();
    }

    @Test
    public void NegativeIndex() {
        helpFeatures();
    }

    @Test
    public void NullDereference() {
        helpFeatures();
    }

    @Test
    public void NegativeArraySize() {
        helpFeatures();
    }

    @Test
    public void ArrayStore() {
        helpFeatures();
    }

    @Test
    public void JavaAssertion() {
        helpFeatures();
    }

    @Test
    public void DivideByZero() {
        helpFeatures();
    }



}
