package org.jmlspecs.openjmltest.testcases;


import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.Dir;
import org.jmlspecs.openjmltest.TCBase;
import org.jmlspecs.openjmltest.TestJavaFileObject;
import org.jmlspecs.openjml.Main;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

/** This is the parent class for classes that simply test whether the spec file 
 * for a JDK class parses without error.  There are two methods of creating
 * these tests implemented here.
 * <P>
 * One is to create a TestSuite, and dynamically add to it an individual test
 * for each class found.  That construction has to be done statically.  It has
 * the advantage that each test appears in the JUnit list of tests and marked
 * as successful or not.  The individual tests can be rerun from the JUnit
 * test runner, but the suite as a whole cannot.  The suite can be run as a
 * Run Configuration.  Another advantage is that the tests can
 * be canceled while in progress.
 * <P>
 * A second implementation, currently disabled, has SpecsBase consisting of
 * just one test, that loops through all the classes being tested.  A disadvantage
 * is that one cannot cancel the tests while in progress and they do not appear
 * in the JUnit listing.  They can also be run from the RunConfiguration.  To
 * enable this mode, comment out the suite() and runTest() methods.
 * 
 * <P>
 * Alternatively, you can create explicit tests for individual system classes.
 * The template is the following:
 * 
 *<PRE>
    public void testFile() {
        checkClass("<fully-qualified-type-name>");
    }
   </PRE>
 * or
 *<PRE>
    public void testFile() {
        helpTCF("A.java","public class A { <fully-qualified-type-name> f; }"
                );
    }
   </PRE>
 *
 *For generic classes (with one type argument) write
 *<PRE>
    public void testFile() {
        checkClassGeneric("<fully-qualified-type-name>");
    }
   </PRE>
 * or
 *<PRE>
    public void testFile() {
        helpTCF("A.java","public class A { <fully-qualified-type-name><?> f; }"
                );
    }
   </PRE>
 *
 * Note also that no errors are reported if there is no specification file or 
 * the class path is such that the spec file is not found.
 * 
 * @author David Cok
 *
 */
// Note - this does not test spec files that are hidden by a later version
//   you need to rerun Eclipse with a different JDK and correspondingly different
//   specifications path.  You can do this with separate Run Configurations.

// At one point in development, running these tests would cause later tests in
// the JUnit sequence to fail, when they would not fail otherwise.  Before that
// problem could be solved, it disappeared, so its cause and resolution are
// unknown.  For now we will leave these tests in, but beware that this was once
// the case and may crop up again in the future.

// Since these tests are a bit time-consuming (about 2 min right now) and will be
// more so as more spec files are added, you can turn them off with the dotests
// flag.

@RunWith(Parameterized.class)
public class SpecsBase extends TCBase {

    /** Enables or disables this suite of tests */
    static private boolean dotests = true;  // Change this to enable/disable dynamic tests
    
    /** If true, then a progress message is printed as each test is executed.*/
    private static boolean verbose = false;

    @Parameters
    static public  Collection<String[]> datax() {
        if (!dotests) return new ArrayList<String[]>(0);
        Collection<String[]> data = new ArrayList<String[]>(1000);
        for (String f: findAllFiles(null)) {
            data.add(new String[]{ f});
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
    public SpecsBase(String classname) {
        this.classname = classname;
    }


    @Override
    public void setUp() throws Exception {
        useSystemSpecs = true;
        super.setUp();
        // We turn off purity checking because there are too many purity errors in the specs to handle right now. (TODO)
        JmlOption.setOption(context,JmlOption.PURITYCHECK,false);
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
        print = false; // true = various debugging output
    }
    
    /** Set to true if errors are found in any test in checkFiles */
    protected boolean foundErrors;
    
    /** Helper method that executes a test 
     * 
     * @param filename name to use for the pseudo source file
     * @param s the code for the pseudo source file
     * @param testClass class being tested, for output only
     */
    //@ modifies foundErrors;
    public void helpTCFile(String filename, String s, String testClass) {
        try {
            JavaFileObject f = new TestJavaFileObject(filename,s);
            if (filename != null) addMockFile("#B/" + filename,f);
            Log.instance(context).useSource(f);
            List<JavaFileObject> files = List.of(f);
            int ex = main.compile(new String[]{}, null, context, files, null).exitCode;
            if (print) JmlSpecs.instance(context).printDatabase();
            int expected = expectedExit;
            if (expected == -1) expected = collector.getDiagnostics().size() == 0 ? 0 : 1;
            if (ex != expected) {
                System.out.println("Unexpected return code for "  + testClass + " actual: " + ex + " expected: " + expected);
                foundErrors = true;
            }
            if (collector.getDiagnostics().size() != 0) {
                System.out.println("ERRORS FOUND " + testClass);
                foundErrors = true;
                printDiagnostics();
            }
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + testClass + " " + e);
        } catch (AssertionError e) {
            if (!print && !noExtraPrinting) printDiagnostics();
            throw e;
        }
        assertTrue("Found errors checking specs for " + testClass, !foundErrors);
    }

    /** This test tests the file that is named as classname by the constructor */
    @Test
    public void testSpecificationFile() {
        foundErrors = false;
        checkClass(classname);
        assertTrue("Errors found",!foundErrors);
    }
    
    // This runs all classes as one test.
    /** The test to run - finds all system specs and runs tests on them in order
     * to at least be sure that the specifications parse and typecheck.
     */
    public void testSpecificationFiles() {
        if (!dotests) {
            System.out.println("System spec tests (test.SpecBase) are being skipped " + System.getProperty("java.version"));
            return;
        }
        foundErrors = false;
        helpTCF("AJDK.java","public class AJDK {  }");  // smoke test
        SortedSet<String> classes = findAllFiles(specs); 
        checkClasses(classes);
        assertTrue("Errors found",!foundErrors);
    }
    
    /** The test to run - finds all system specs and runs tests on them that
     * at least are sure that the specifications parse and typecheck.
     */
    static public SortedSet<String> findAllFiles(/*@ nullable*/ JmlSpecs specs) {
        System.out.println("JRE version " + System.getProperty("java.version"));
        try {
            if (specs == null) {
                Main main = new Main();
                Context context = main.context();
                specs = JmlSpecs.instance(context);
                specs.setSpecsPath("$SY");
            }
        } catch (IOException e) {
            e.printStackTrace();
            fail("Exception in findAllFiles");
        }
        java.util.List<Dir> dirs = specs.getSpecsPath();
        assertTrue ("Null specs path",dirs != null); 
        assertTrue ("No specs path",dirs.size() != 0); 
        
        SortedSet<String> classes = new TreeSet<String>(); 
        for (Dir dir: dirs) {
            File d = new File(dir.toString());
            classes.addAll(findAllFiles(d, dir.toString()));
        }
        classes.removeAll(donttest);
        System.out.println(classes.size() + " system specification classes found");
        return classes;
    }
    
    /** Set of classes (fully qualified, dot-separated names) that should not
     * be tested.
     */
    static Set<String> donttest = new HashSet<String>();
    static {
        donttest.add("java.lang.StringCoding"); // (FIXME) Turn this off because it is not public 
    }
    
    /** Creates a list of all the files (of any suffix), interpreted as fully-qualified Java class 
     * names when the root prefix is removed,
     * recursively found underneath the given directory
     * @param d the directory in which to search
     * @param root the prefix of the path to ignore
     * @return list of dot-separated class names for which files were found
     */
    static public java.util.List<String> findAllFiles(File d, String root) {
        String[] files = d.list();
        java.util.List<String> list = new ArrayList<String>();
        if (files == null) return list;
        for (String s: files) {
            if (s.charAt(0) == '.') continue;
            File f = new File(d,s);
            if (f.isDirectory()) {
                list.addAll(findAllFiles(f, root));
            } else {
                String ss = f.toString().substring(root.length()+1);
                int p = ss.lastIndexOf('.');
                ss = ss.substring(0,p).replace(File.separatorChar,'.');
                list.add(ss);
            }
        }
        return list;
    }

    /** Does a test on each class in the given set of fully qualified,
     * dot-separated class names
     * 
     * @param classNames set of classes to test
     */
    //@ modifies foundErrors;
    public void checkClasses(Set<String> classNames) {
        for (String qname: classNames) {
            int n = isGeneric(qname);
            if (n == 1) checkClassGeneric(qname);
            else if (n == 0) checkClass(qname);
            else {
                assertTrue("Not implemented for " + n + " + generic arguments",false);
            }
        }
    }

    /** Does a test on the given fully qualified,
     * dot-separated class name
     * 
     * @param className the name of the class to test
     */
    //@ modifies foundErrors;
    public void checkClass(String className) {
        String program = "public class AJDK { "+ className +" o; }";
        if (verbose) System.out.println("JUnit SpecsBase: " + className);
        helpTCFile("AJDK.java",program,className);
    }
    
    /** Does a test on the given fully qualified,
     * dot-separated class name
     * 
     * @param className the name of the class to test
     */
    //@ modifies foundErrors;
    public void checkClassGeneric(String className) {
        String program = "public class AJDK { "+ className +"<?> o; }";
        if (verbose) System.out.println("JUnit SpecsBase: " + className);
        helpTCFile("AJDK.java",program,className);
    }
    
    /** Returns the number of generic type arguments
     * @param className the class in question
     * @return the number of generic type arguments
     */
    public int isGeneric(String className) {
        if ("java.util.LinkedList".equals(className)) return 1;
        if ("java.util.AbstractQueue".equals(className)) return 1;
        if ("java.util.ArrayDeque".equals(className)) return 1;
        if ("java.util.Deque".equals(className)) return 1;
        return 0;
    }
    
    // FIXME - the above test template does not seem to trigger all the
    // modifier checking in attribute testing.

    /** Use this to test the specs for a specific file. Enable it by
     * adding an @Test as an annotation. */
    
    // @Test
    public void testFileTemp() {
        checkClassGeneric("java.util.LinkedList");
    }

}
