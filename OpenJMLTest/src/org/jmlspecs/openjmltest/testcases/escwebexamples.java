package org.jmlspecs.openjmltest.testcases;

import java.io.File;

import org.jmlspecs.openjmltest.EscBase;
import org.junit.Assert;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check examples in the online web pages (openjml.github.io/examples).
 * The expected results are kept in OpenJMLTest/test/webexamples.
 * FIXME - ought to have a check that all the given examples are tested
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escwebexamples extends EscBase {
    
    final String sources = "../../openjml.github.io/examples/";
    final String expected = "test/webexamples/";

    @Override
    public void setUp() throws Exception {
        super.setUp();
    	ignoreNotes = true;
    }
    
    public void helpTG() {
        String testFileroot = getMethodName(1);
        Assert.assertTrue("Web example sources not found", new File(sources).exists() && new File(sources).isDirectory());
        Assert.assertTrue("Expected location not found", new File(expected).exists() && new File(expected).isDirectory());
        escOnFiles(sources + testFileroot + ".java", expected + testFileroot, "--progress", "--solver-seed=42");
    }
    
    @Test  // This one non-deterministically timesout - hence the fixing of solver-seed
    public void HeapSort() {
        helpTG();
    }

    @Test
    public void SelectionSort() {
        helpTG();
    }

    @Test
    public void BubbleSort() {
        helpTG();
    }

    @Test
    public void MergeSort() {
        helpTG();
    }

 
}
