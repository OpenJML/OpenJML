package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.RacBase;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;


/** This suite of tests runs openjml --rac on a set of custom written test files that
 * exercise (ideally all) the Java functionality and JML specifications of a given Java library class.
 * These custom written test files are contained in subfolders of the OpenJMLTest/testspecs folder.
 * Those subfolders have names that are fully-qualified class names, but with '.' replaced by '-'.
 * Within the folder is a .java file whose content exercises the class's functionality and
 * are meant to be checked with RAC using the JML specifications for the class.
 * The expected output from the application of openjml --rac is found in the file named 'expected-compile'
 * in that same folder. After successful compilation, the compiled program is run using openjml-java
 * and the output is expected to match that in 'expected-run'.
 * 
 * Note that the specifications in the library class's .jml file will largely be unused in this testing,
 * because it is not compiled into the library's .class file for the class. Instead the behavior of the 
 * class is checked against the assertions in the test program, which assertions are those proved valid
 * by the companion tests in SpecsEsc.
 * 
 * This suite is a parameterized JUnit test suite, where the parameters are the names of the classes
 * to be tested.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SpecsRac extends RacBase {

    /** The name of the subfolder of OpenJMLTest that holds the data for this suite */
    public static final String testdir = "testspecs";
    
    /** Returns the parameters for this parameterized test suite */
    @Parameters
    static public  Collection<String[]> datax() {
        Collection<String[]> data = new ArrayList<String[]>(1000);
        for (File f: findAllFiles()) {
            data.add(new String[]{ f.getName()});
        }
        return data;
    }

    /** The name of the folder to be tested (which is also the name of the test),
     * filled in by the constructor when called by the test infrastructure.
     */
    /*@ non_null*/
    private String foldername;
    
    public SpecsRac(String foldername) {
        this.foldername = foldername;
    }


    @Override
    public void setUp() throws Exception {
        super.setUp();
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
    }
    
    /** This test tests the folder that is named as foldername by the constructor.
     * The file within the folder whose name begins with 'Test' is presumed to contain 
     * the 'main' method used to run the RAC-compiled program. */
    @Test
    public void testSpecificationFile() {
        expectedExit = 0;
        ignoreNotes = true;
        String subdir = testdir + "/" + foldername;
        String testname = null;
        for (File f: new File(subdir).listFiles()) {
            if (f.getName().startsWith("Test")) {
                testname = f.getName().replace(".java","");
                break;
            }
        }
        helpRac(subdir,subdir,testname);
    }
    
    static public java.util.List<File> findAllFiles() {
        File dir = new File("testspecs");
        java.util.List<File> folders = new ArrayList<>();
        for (File f: dir.listFiles()) if (f.isDirectory()) folders.add(f);
        System.out.println(folders.size() + " system specification classes found for rac testing");
        return folders;
    }
}
