package org.jmlspecs.openjmltest.testsuites;

import java.io.File;

import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check examples in the online web pages (openjml.github.io/examples).
 * The expected results are kept in OpenJMLTest/test/webexamples.
 * FIXME - ought to have a check that all the given examples are tested
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escwebexamples extends EscBaseFiles {
    
    final String sources = "../../openjml.github.io/examples/";
    final String expected = "test/escwebexamples/";

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--no-infer=show");
    }
    
    public void helpEscSimple() {
        String testFileroot = getTestName();
        Assert.assertTrue("Web example sources not found", new File(sources).exists() && new File(sources).isDirectory());
        Assert.assertTrue("Expected location not found", new File(expected).exists() && new File(expected).isDirectory());
        escOnFiles(sources + testFileroot + ".java", expected + testFileroot, "--progress", "--solver-seed=42");
    }
    
    @Test  // This one non-deterministically timesout - hence the fixing of solver-seed
    public void HeapSort() {
        helpEscSimple();
    }

    @Test
    public void SelectionSort() {
        helpEscSimple();
    }

    @Test
    public void BubbleSort() {
        helpEscSimple();
    }

    @Test
    public void MergeSort() {
        helpEscSimple();
    }

 
}
