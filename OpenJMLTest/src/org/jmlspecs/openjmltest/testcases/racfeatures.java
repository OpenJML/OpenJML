package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjmltest.RacBase;
import org.junit.Before;
import org.junit.Test;

/** These tests run rac on the demo files in OpenJMLDemo/src/features
 *  The expected results are in OpenJMLTest/test/features
 *  The class files from compilation are in OpenJMLTest/testcompiles
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
public class racfeatures extends RacBase {

    @Override
    @Before
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
    }
    
    // The R version runs with --rac-java-checks (but currently no other of the supplied options)
    public void helpFeature(String n, String ... options) {
        helpTCF(OpenJMLDemoPath + "/src/features/"+n+".java","test/features/"+n,"features."+n, options);
        helpTCF(OpenJMLDemoPath + "/src/features/"+n+".java","test/features/"+n+"R","features."+n, "--rac-java-checks");
    }
    
    public void helpFeature() {
        helpFeature(getMethodName(1));
    }

    
    
    @Test
    public void NegativeArraySize() {
        expectedRACExit = 1;
        helpFeature();
    }

    @Test
    public void JavaAssertion() {
        expectedRACExit = 1;
        helpFeature();
    }

    @Test
    public void ArrayStore() {
        expectedRACExit = 0;
        helpFeature();
    }


}
