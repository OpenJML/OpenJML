package org.jmlspecs.openjmltest.testcases;


import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.Dir;
import org.jmlspecs.openjmltest.RacBase;
import org.jmlspecs.openjmltest.TCBase;
import org.jmlspecs.openjmltest.TestJavaFileObject;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Utils;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;


@RunWith(Parameterized.class)
public class SpecsRac extends RacBase {

    /** Enables or disables this suite of tests */
    static private boolean dotests = true;  // Change this to enable/disable dynamic tests
    
    /** If true, then a progress message is printed as each test is executed.*/
    private static boolean verbose = false;

    @Parameters
    static public  Collection<String[]> datax() {
        if (!dotests) return new ArrayList<String[]>(0);
        Collection<String[]> data = new ArrayList<String[]>(1000);
        for (File f: findAllFiles()) {
            data.add(new String[]{ f.getName()});
        }
        return data;
    }

    /** The name of the class to be tested (which is also the name of the test)
     * when the suite mode is used. This is defined simply to enable debugging.
     */
    /*@ non_null*/
    private String classname;
    
    /** We use SpecsBase as a test case, with a name and its own runTest, to
     * execute the test on a given class name.
     * @param classname the fully qualified class to test
     */
    public SpecsRac(String classname) {
        this.classname = classname;
    }


    @Override
    public void setUp() throws Exception {
        super.setUp();
        // We turn off purity checking because there are too many purity errors in the specs to handle right now. (TODO)
        JmlOption.setOption(context,JmlOption.PURITYCHECK,false);
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
        print = false; // true = various debugging output
    }
    
    /** Set to true if errors are found in any test in checkFiles */
    protected boolean foundErrors;
    
//    /** Helper method that executes a test 
//     * 
//     * @param filename name to use for the pseudo source file
//     * @param s the code for the pseudo source file
//     * @param testClass class being tested, for output only
//     */
//    //@ modifies foundErrors;
//    public void helpTCFile(String filename, String s, String testClass) {
//        try {
//            JavaFileObject f = new TestJavaFileObject(filename,s);
//            if (filename != null) addMockFile("#B/" + filename,f);
//            Log.instance(context).useSource(f);
//            List<JavaFileObject> files = List.of(f);
//            int ex = main.compile(new String[]{}, null, context, files, null).exitCode;
//            if (print) JmlSpecs.instance(context).printDatabase();
//            int expected = expectedExit;
//            if (expected == -1) expected = collector.getDiagnostics().size() == 0 ? 0 : 1;
//            if (ex != expected) {
//                System.out.println("Unexpected return code for "  + testClass + " actual: " + ex + " expected: " + expected);
//                foundErrors = true;
//            }
//            if (collector.getDiagnostics().size() != 0) {
//                System.out.println("ERRORS FOUND " + testClass);
//                foundErrors = true;
//                printDiagnostics();
//            }
//        } catch (Exception e) {
//            e.printStackTrace(System.out);
//            fail("Exception thrown while processing test: " + testClass + " " + e);
//        } catch (AssertionError e) {
//            if (!print && !noExtraPrinting) printDiagnostics();
//            throw e;
//        }
//        assertTrue("Found errors checking specs for " + testClass, !foundErrors);
//    }

    /** This test tests the file that is named as classname by the constructor */
    @Test
    public void testSpecificationFile() {
    	expectedExit = 0;
    	String subdir = "testspecs" + "/" + classname;
    	helpTCF(subdir,subdir,"Test"+classname);
    }
    
    static public java.util.List<File> findAllFiles() {
        File dir = new File("testspecs");
        java.util.List<File> classes = new ArrayList<>();
        for (File f: dir.listFiles()) if (f.isDirectory()) classes.add(f);
        System.out.println(classes.size() + " system specification classes found for rac testing");
        return classes;
    }
    
//    /** Set of classes (fully qualified, dot-separated names) that should not
//     * be tested.
//     */
//    static Set<String> donttest = new HashSet<String>();
//    static {
//        donttest.add("java.lang.StringCoding"); // (FIXME) Turn this off because it is not public 
//    }
//    
//    static java.util.HashMap<String,Integer> counts = new java.util.HashMap<>();
    
    
 
//    /** Use this to test the specs for a specific file. Enable it by
//     * adding an @Test as an annotation. */
//    
//    // @Test
//    public void testFileTemp() {
//        checkClass("java.util.LinkedList", 1);
//    }

}
