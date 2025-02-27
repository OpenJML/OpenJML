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
    
    // This version compiles and runs twice: once with the given options and once with just --rac-java-checks
    public void helpFeature(String n, String ... options) {
        helpTCF(OpenJMLDemoPath + "/src/features/"+n+".java","test/features/"+n,"features."+n, options);
        helpTCF(OpenJMLDemoPath + "/src/features/"+n+".java","test/features/"+n+"R","features."+n, "--rac-java-checks");
    }
    
    // This version compiles twice: once with no options and once with just --rac-java-checks, using the method name as the test name
    public void helpFeature() {
        helpFeature(getTestName());
    }

    // This version compiles and runs once
    public void helpFeature1(String n, String ... options) {
        helpTCF(OpenJMLDemoPath + "/src/examples/"+n,"test/features/"+n,"EntryPreconditionTest", options);
    }
    
    
    @Test
    public void EntryPrecondition() {
        helpFeature1("EntryPrecondition","--rac-check-assumptions","--rac-precondition-entry");
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
    public void DivideByZero() {
        expectedRACExit = 1;
        helpFeature();
    }

    @Test
    public void NullDereference() {
        expectedRACExit = 1;
        helpFeature();
    }

    @Test
    public void IndexOutOfRange() {
        expectedRACExit = 1;
        helpFeature();
    }

    @Test
    public void NegativeIndex() {
        expectedRACExit = 1;
        helpFeature();
    }

    @Test
    public void ArrayStore() {
        expectedRACExit = 0;
        helpFeature();
    }


}
