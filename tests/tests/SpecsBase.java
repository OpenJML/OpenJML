package tests;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import javax.tools.JavaFileObject;

import junit.framework.AssertionFailedError;

import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.Dir;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

/** This is the parent class for classes that simply test whether the spec file 
 * for a JDK class parses without error.  The 'testFiles' test dynamically 
 * creates and tests source code for each specification file that is found
 * in the specification path (which is set to contain just the system specification
 * directories).
 * <P>
 * Alternatively, you can create explicit tests for individual system classes.
 * The template is the following:
 * 
 *<PRE>
    public void testFile() {
        helpTCF("A.java","public class A { <fully-qualified-type-name> f; }"
                );
    }
   </PRE>
 *
 * Note that no errors are also reported if there is no specification file or 
 * the class path is such that the spec file is not findable.
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
public class SpecsBase extends TCBase {

    private boolean dotests = true;  // Change this to enable/disable tests
    
    protected void setUp() throws Exception {
        if (dotests) {
            //testspecpath1 = "$SY";
            useSystemSpecs = true;
        }
        super.setUp();
        JmlOptionName.putOption(context,JmlOptionName.NOPURITYCHECK);
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
        print = false;
    }
    
    /** Set to true if errors are found in any test in checkFiles */
    boolean foundErrors;
    
    /** Helper method that executes a test 
     * 
     * @param filename name to use for the pseudo source file
     * @param s the code for the pseudo source file
     * @param testClass class being tested, for output only
     */
    //@ modifies foundErrors;
    public void helpTCFile(String filename, String s, String testClass) {
        try {
            setUp();
            JavaFileObject f = new TestJavaFileObject(filename,s);
            if (filename != null) addMockFile("#B/" + filename,f);
            Log.instance(context).useSource(f);
            List<JavaFileObject> files = List.of(f);
            int ex = main.compile(new String[]{}, context, files, null);
            if (print) JmlSpecs.instance(context).printDatabase();
            if (ex != 0) {
                System.out.println("Unexpected return code for "  + testClass + " " + ex);
                foundErrors = true;
            }
            if (collector.getDiagnostics().size() != 0) {
                System.out.println("ERRORS FOUND " + testClass);
                foundErrors = true;
                printErrors();
            }
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionFailedError e) {
            if (!print && !noExtraPrinting) printErrors();
            throw e;
        }
    }

    /** The test to run - finds all system specs and runs tests on them that
     * at least are sure that the specifications parse and typecheck.
     */
    public void testFindFiles() {
        if (!dotests) {
            System.out.println("System spec tests (test.SpecBase) are being skipped " + System.getProperty("java.version"));
            return;
        }
        System.out.println("JRE version " + System.getProperty("java.version"));
        foundErrors = false;
        helpTCF("AJDK.java","public class AJDK {  }");
        java.util.List<Dir> dirs = specs.getSpecsPath();
        assertTrue ("Null specs path",dirs != null); 
        assertTrue ("No specs path",dirs.size() != 0); 
        SortedSet<String> classes = new TreeSet<String>(); 
        for (Dir dir: dirs) {
            File d = new File(dir.toString());
            classes.addAll(findAllFiles(d, dir.toString()));
        }
        classes.removeAll(donttest);
        checkFiles(classes);
        assertTrue("Errors found",!foundErrors);
        System.out.println(classes.size() + " system specification classes tested");
    }
    
    /** Set of classes (fully qualified, dot-separated names) that should not
     * be tested.
     */
    Set<String> donttest = new HashSet<String>();
    {
        donttest.add("java.lang.StringCoding"); // Turn this off because it is not public (FIXME)
    }
    
    /** Creates a list of all the files (of any suffix), interpreted as fully-qualified Java class 
     * names when the 'root; prefix is removed,
     * recursively found underneath the given directory
     * @param d the directory in which to search
     * @param root the prefix of the path to ignore
     * @return list of dot-separated class names for which files were found
     */
    public java.util.List<String> findAllFiles(File d, String root) {
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
    public void checkFiles(Set<String> classNames) {
        for (String qname: classNames) {
            String program = "public class AJDK { "+ qname +" o; }";
            System.out.println("JUnit SpecsBase: " + qname);
            helpTCFile("AJDK.java",program,qname);
        }
    }

//    public void testFileTemp() {
//        helpTCF("A.java","public class A { java.util.GregorianCalendar f; }"
//                );
//    }

}
