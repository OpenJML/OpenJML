package tests;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import junit.framework.AssertionFailedError;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.Dir;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

/** This is the parent class for classes that simply test whether the spec file for a JDK class parses correctly.  Simply create a
 * derived test of the form
 * 
 *<PRE>
    public void testFile() {
        helpTCF("A.java","public class A { java.io.File f; }"
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
// FIXME - create a test that makes sure the class path is finding specs
// FIXME - make the path more robust across different environments
// FIXME - check that all jdk files are actually tested
// FIXME - enabling this interferes with some later tests
public class SpecsBase extends TCBase {

    boolean dotests = false;
    
    protected void setUp() throws Exception {
        if (dotests) testspecpath1 = "../../../JMLspecs/trunk/java6"+z+"../../../JMLspecs/trunk/java5" + z+"../../../JMLspecs/trunk/java4";
        super.setUp();
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
        print = false;
    }
    
    boolean foundErrors;
    
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

    
    public void testFindFiles() {
        if (!dotests) return;
        foundErrors = false;
        helpTCF("AJDK.java","public class AJDK {  }");
        java.util.List<Dir> dirs = specs.getSpecsPath();
        assertTrue ("Null specs path",dirs != null); 
        assertTrue ("No specs path",dirs.size() != 0); 
        for (Dir dir: dirs) {
            File d = new File(dir.toString());
            checkAllFiles(d, dir.toString());
        }
        assertTrue("Errors found",!foundErrors);
    }
    
    Set<String> donttest = new HashSet<String>();
    {
        donttest.add("java.lang.StringCoding");
    }
    
    public void checkAllFiles(File d, String root) {
        String[] files = d.list();
        if (files == null) return;
        for (String s: files) {
            if (s.charAt(0) == '.') continue;
            File f = new File(d,s);
            if (f.isDirectory()) {
                checkAllFiles(f, root);
            } else {
                String ss = f.toString().substring(root.length()+1);
                // Is there a test for f
                int p = ss.lastIndexOf('.');
                ss = ss.substring(0,p).replace(File.separatorChar,'.');
                if (donttest.contains(ss)) continue;
                String program = "public class AJDK { "+ss+" o; }";
                System.out.println("TESTING " + ss);
                helpTCFile("AJDK.java",program,ss);
            }
        }
    }


}
