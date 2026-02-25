package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.jmlspecs.openjml.Dir;
///import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.Main;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

import javax.tools.JavaFileObject;

import static org.junit.Assert.*;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.MockJavaFileObject;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

/** This test suite finds each of the specification (.jml) files in the 
 * library specifications, creates a temporary .java file that simply declares
 * a field of the class for that specification file, and then runs
 * openjml --check on that .java file. The effect is to test that the
 * library .jml file parses and type checks without error, with reference to the 
 * corresponding binary for the class.
 * 
 * Some classes (cf. the list 'donttest') and some packages are excluded from
 * being tested.
 * 
 * The location of the specification files is given by Main.specs, that is
 * by the OPENJML_SPECS environment variable, which is setup in the
 * runtests scriot.
 */

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SpecsBase extends TCBase {
    
    public static final String testdir = "testspecs"; // The subfolder of OpenJMLTest/test that contains expected results from these tests

    /** This method creates the list of classnames to be tested, for this
     * parameterized suite of JUnit tests.
     * Each item in the collection is a 1-element array that gives the actual argument
     * of the one-argument constructor of SpecsBase.
     */
    @Parameters
    static public Collection<String[]> datax() {
        Collection<String[]> data = new ArrayList<String[]>(1000);
        for (String f: findAllFiles()) {
            data.add(new String[]{ f});
        }
        return data;
    }

    /** The name of the class to be tested (which is also the name of the test);
     * it is set by the constructor for each test in turn.
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
    
    public static String jarString;

    /** Deletes any files whose names end in 'actual' from the testspecs folder,
     * and checks that the specs folder exists and sets up jarstring */
    @BeforeClass
    public static void clean() {
        var ts = new File(testdir);
        if (ts.exists()) {
            for (var f : ts.listFiles((ff,nm)->nm.endsWith("actual"))) f.delete();
        }
        assertTrue("Specifications folder does not exist: " + Main.specs, new File(Main.specs).exists());
    }

    @Override @Before
    public void setUp() throws Exception {
        ignoreNotes = false;
        //print = printDiagnostics = true; // true = various debugging output
        super.setUp();
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
    }
    
    /** This is the entry point of the test, which tests the file that is named as classname by the constructor.
     */
    @Test
    public void testSpecificationFile() {
        checkClass(classname);
    }
    
    /** Does a test on the given fully qualified, dot-separated class name
     * 
     * @param className the name of the class to test
     */
    public void checkClass(String className) {
        try {
            Class<?> clazz = Class.forName(className);
            var typeParameters = clazz.getTypeParameters();
            int numTypeArgs = typeParameters.length;

            String program = "public class AJDK { "+ className + typeargs[numTypeArgs] + " o; }";
            // These two take special treatment because they may not have a field
            if (className.equals("org.jmlspecs.lang.internal.range")) program = "public class AJDK { public void m(org.jmlspecs.lang.internal.range o) {} }"; // cf. primesc.jmldatagroup, primrac.jmldatagroup for full tests
            if (className.equals("org.jmlspecs.lang.internal.datagroup")) program = "public class AJDK { /*@ model public \\datagroup d; */ }"; // cf. primesc.jmldatagroup, primrac.jmldatagroup, primTC.jmldatagroup for full tests

            String filename = "AJDK.java";
            var testClass = className;
            
            String foundError = null;

            JavaFileObject f = new MockJavaFileObject(filename,program);
            addMockFile("#B/" + filename,f);
            Log.instance(context).useSource(f);
            List<JavaFileObject> files = List.of(f);
            // We turn off purity checking because there are too many purity errors in the specs to handle right now. (TODO)
            int ex = main.compile(new String[]{
                    "-Xlint:removal","-Xlint:deprecation"},
                    files).exitCode;
            int expected = expectedExit;
            boolean allNotes = collector.getDiagnostics().stream().allMatch(d->d.toString().contains("Note:"));
            boolean anyErrors = collector.getDiagnostics().stream().anyMatch(d->d.toString().contains("error:"));
            if (expected == -1) expected = !anyErrors ? 0 : 1;
            if (ex != expected) {
                foundError = "Unexpected return code  actual: " + ex + " expected: " + expected;
            }
            String expfile = testdir + "/" + testClass + "-expected";
            String actfile = testdir + "/" + testClass + "-actual";
            if (!allNotes) {
                String act = diagnosticsToString(collector.getDiagnostics());
                if (new java.io.File(expfile).exists()) {
                    String exp = java.nio.file.Files.readString(Paths.get(expfile));
                    if (!exp.equals(act)) {
                        foundError = "unexpected output";
                        this.out.println(act);
                        java.nio.file.Files.writeString(Paths.get(actfile), act);
                    } else {
                        // this.out.println("Output matched for " + testClass);
                        new java.io.File(actfile).delete();
                    }
                } else {
                    java.nio.file.Files.writeString(Paths.get(actfile), act);
                    foundError = "Errors found but no corresponding expected file";
                    printDiagnostics();
                }
            } else { // No output (except notes)
                if (new java.io.File(expfile).exists()) {
                    // If there is no output there should not be an expected test
                    foundError = "No test output but there is an expected output file";
                }
            }
            assertTrue("Found errors checking specs for " + foundError, foundError == null);
        } catch (Exception e) {
            e.printStackTrace(this.out);
            fail("Failed to test " + className + ": " + e);
        }
    }
    // FIXME - the above test template does not seem to trigger all the
    // modifier checking in attribute testing.
    
    /** Finds all classes that have library specification files.
     * Output is the filename with '/' separators
     */
    static public SortedSet<String> findAllFiles() {
        System.out.println("JRE version " + System.getProperty("java.version"));
        var dir = new Dir.FileSystemDir(Main.specs);
        
        SortedSet<String> classes = new TreeSet<String>(); 
        File d = new File(dir.toString());
        classes.addAll(findAllFiles(d, dir.toString()));
        classes.removeAll(donttest);
        classes.removeIf(f->exclude(f));
        System.out.println(classes.size() + " system specification classes found");
        return classes;
    }

    /** Creates a list of all the files (of any suffix), interpreted as fully-qualified Java class 
     * names when the root prefix is removed, recursively found underneath the given directory
     * @param d the directory in which to search
     * @param root the prefix of the path to ignore
     * @return list of dot-separated class names for which files were found
     */
    static private java.util.List<String> findAllFiles(File d, String root) {
        String[] files = d.list();
        java.util.List<String> list = new ArrayList<String>();
        if (files == null) return list;
        for (String s: files) {
            if (s.charAt(0) == '.') continue;
            File f = new File(d,s);
            if (f.isDirectory()) {
                list.addAll(findAllFiles(f, root));
            } else {
                processFile(root, list, f);
            }
        }
        return list;
    }

    /** Set of classes (fully qualified, dot-separated names) that should not be tested.
     */
    static Set<String> donttest = new HashSet<String>();
    static {
       // donttest.add("org.junit.Assert"); // (FIXME) Turn this off because the test does not find the junit library 
        donttest.add("java.lang.AbstractStringBuilder"); // FIXME - not public
        donttest.add("java.lang.StringCoding");
        donttest.add("org.hamcrest.Matchers");
        donttest.add("org.jmlspecs.lang.internal.range"); // See specialized test below
    }
    
    /** Returns true for any filepath that should not be tested */
    public static boolean exclude(String classname) {
        if (classname.startsWith("org.jmlspecs.models")) return true; // FIXME - eventually support or delete these
        if (classname.startsWith("Array")) return true;
        if (classname.startsWith("java.awt")) return true;
        if (classname.startsWith("javax.swing")) return true;
        return false;
    }
    
    private static void processFile(String root, java.util.List<String> list, File f) {
        String qualifiedName = f.toString().substring(root.length()+1);
        int p = qualifiedName.lastIndexOf('.');
        String baseName = qualifiedName.substring(0,p);
        baseName = baseName.replace(File.separatorChar,'.');
        if (exclude(baseName)) return;
        if (qualifiedName.substring(p).equals(".jml")) list.add(baseName);
        else System.out.println("IGNORING FILE " + qualifiedName + " in " + root);
    }
    
    /** Needs as many entries as the most type arguments that will be found */
    String[] typeargs = { "", "<?>", "<?,?>", "<?,?,?>", "<?,?,?,?>", "<?,?,?,?,?>" };
}
