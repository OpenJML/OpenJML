package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.EscBaseFiles;
import org.jmlspecs.openjmltest.JmlTestSuite;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.Strings;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** This suite of tests runs openjml --esc on a set of custom written test files that
 * exercise (ideally all) the Java functionality and JML specifications of a given Java library class.
 * These custom written test files are contained in subfolders of the OpenJMLTest/testspecs folder.
 * Those subfolders have names that are fully-qualified class names, but with '.' replaced by '-'.
 * Within the folder are one or more .java files whose content exercise the class's functionality and
 * are meant to be proven valid using the JML specifications for the class.
 * The expected output from the application of openjml --esc is found in the file named 'expected'
 * in that same folder.
 * 
 * This suite is a parameterized JUnit test suite, where the parameters are the names of the classes
 * to be tested.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SpecsEsc extends EscBaseFiles {

    /** The name of the subfolder of OpenJMLTest that holds the data for this suite */
    public static final String testdir = "testspecs";
    
    /** Returns the parameters for this parameterized test suite */
    @Parameters
    static public  Collection<String[]> datax() {
        ArrayList<String[]> data = new ArrayList<String[]>(1000);
        for (File f: findAllFiles()) {
            data.add(new String[]{ f.getName()});
        }
        java.util.Collections.sort(data, ((t1,t2)->t1[0].compareTo(t2[0])));
        return data;
    }

    /** The name of the folder to be tested (which is also the name of the test). 
     * The foldername is the classname with '.' replaced by '-'.
     * This value is filled in by the constsructor, when it is called by the test infrastructure.
     */
    /*@ non_null*/
    private String foldername;
    
    /** We use SpecsBase as a test case, with a name and its own runTest, to
     * execute the test on a given class name.
     * @param classname the fully qualified class to test
     */
    public SpecsEsc(String foldername) {
        super("", "z3_4_3");  // FIXME - allow solvers
        this.foldername = foldername;
    }


    @Override @org.junit.Before
    public void setUp() throws Exception {
        super.setUp();
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
    }
    
    /** This test tests the file that is named as classname by the constructor */
    @Test
    public void testSpecificationFile() {
        String subdir = JmlTestSuite.root + "/OpenJML/OpenJMLTest/" + testdir + "/" + foldername;
        // Note that escOnFiles contributes its own options
        escOnFiles(subdir,subdir,"--exclude=main,<init>","--no-show-skipped","--check-feasibility=return");
    }
    
    static public java.util.List<File> findAllFiles() {
        File dir = new File("testspecs"); // Presumes working directory is OpenJMLTest
        java.util.List<File> classes = new ArrayList<>();
        for (File f: dir.listFiles()) {
            if (f.isDirectory()) classes.add(f);
        }
        System.out.println(classes.size() + " system specification classes found for esc testing");
        return classes;
    }
}
