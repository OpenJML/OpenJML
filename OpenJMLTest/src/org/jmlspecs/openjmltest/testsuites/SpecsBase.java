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
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;

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
 *
 * Each test also checks that the .jml declares every public and protected field, method and constructor that the
 * class itself (not a supertype) declares, as the binary class has them (#1099). A member counts as declared when
 * its specs come from the .jml, the same notion as the jml.undeclared.member warning (JmlAttr.warnUndeclaredMember,
 * #1060). Synthetic and bridge members are skipped, as are implicit ones that javac generates and the class file
 * does not mark (default constructors, enum values()/valueOf), which therefore count like any other member. A
 * public or protected member class is checked the same way, recursively, if the .jml declares it; otherwise only
 * the class itself is reported. A declared method or constructor is also listed, prefixed by 'unspecified ', if its
 * .jml declaration has no specification case and no JML modifier and it overrides nothing (an override inherits
 * its parents' specs). Fields are not checked for specs, since a bare declaration already carries the default
 * nullness.
 *
 * The file testspecs/[class]-declared lists the members known to be undeclared or unspecified, one per line
 * (sorted; nested members prefixed by their class's path, nested classes by 'class '); an absent file means the
 * .jml must be complete. On a mismatch the actual list is written to testspecs/[class]-declared-actual.
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
            // Register by URI in the existing mockFiles (same object as main.mockFiles).
            mockFiles.addMockByUri(f.toUri().normalize(), f);
            // We turn off purity checking because there are too many purity errors in the specs to handle right now. (TODO)
            int ex = main.compile(new String[]{
                    "-Xlint:removal","-Xlint:deprecation", f.getName()},
                    mockFiles).exitCode;
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
            String declError = checkDeclarations(className);
            if (foundError != null && declError != null) foundError += "; " + declError;
            else if (foundError == null) foundError = declError;
            assertTrue("Found errors checking specs for " + foundError, foundError == null);
        } catch (Exception e) {
            e.printStackTrace(this.out);
            fail("Failed to test " + className + ": " + e);
        }
    }
    // FIXME - the above test template does not seem to trigger all the
    // modifier checking in attribute testing.

    /** After checkClass's compile, compares the members of className that its .jml does not declare or specify
     * with testspecs/[className]-declared; returns a description of a mismatch, or null */
    String checkDeclarations(String className) throws IOException {
        ClassSymbol csym = null;
        for (var c: Symtab.instance(context).getClassesForName(Names.instance(context).fromString(className))) csym = c;
        if (csym == null) return "class not found: " + className;
        JmlSpecs specs = JmlSpecs.instance(context);
        if (!fromJml(specs.getLoadedSpecs(csym).specDecl)) return "no .jml specs loaded for " + className;
        var missing = new ArrayList<String>();
        collectUndeclared(specs, csym, "", missing);
        missing.sort(null);

        Path known = Path.of(testdir, className + "-declared");
        Path actual = Path.of(testdir, className + "-declared-actual");
        var expected = new ArrayList<String>();
        if (java.nio.file.Files.exists(known)) {
            for (String line: java.nio.file.Files.readAllLines(known)) if (!line.isBlank()) expected.add(line.trim());
        }
        expected.sort(null);
        if (expected.equals(missing)) return null;
        java.nio.file.Files.write(actual, missing);
        this.out.println("Undeclared or unspecified members of " + className + " differ from " + known + ": " + missing);
        return "undeclared or unspecified members differ from " + known;
    }

    /** Adds to 'missing' the public and protected members of csym that its .jml does not declare, or declares
     * without specs, each prefixed by 'prefix' (the path of a nested class) */
    void collectUndeclared(JmlSpecs specs, ClassSymbol csym, String prefix, java.util.List<String> missing) {
        for (Symbol s: csym.members().getSymbols()) {
            long flags = s.flags();
            if ((flags & (Flags.PUBLIC|Flags.PROTECTED)) == 0 || (flags & (Flags.SYNTHETIC|Flags.BRIDGE)) != 0) continue;
            if (Utils.isJML(flags)) continue; // declared only in the .jml (model and ghost members)
            if (s instanceof MethodSymbol m) {
                var ms = specs.getLoadedSpecs(m);
                if (ms == null || !fromJml(ms.specDecl)) missing.add(prefix + m);
                else if (!hasSpecs(ms.specDecl) && Utils.instance(context).parents(m, false).isEmpty()) missing.add("unspecified " + prefix + m);
            } else if (s instanceof VarSymbol v) {
                var fs = specs.getLoadedSpecs(v);
                if (fs == null || !fromJml(fs.decl)) missing.add(prefix + v);
            } else if (s instanceof ClassSymbol c && c.owner == csym) {
                if (fromJml(specs.getLoadedSpecs(c).specDecl)) {
                    collectUndeclared(specs, c, prefix + c.name + ".", missing);
                } else {
                    missing.add("class " + prefix + c.name);
                }
            }
        }
    }

    /** True if the .jml declaration has a specification case or a JML modifier (e.g. pure, nullable) */
    static boolean hasSpecs(JmlTree.JmlMethodDecl decl) {
        var cases = decl.methodSpecs;
        if (cases != null && (cases.cases.nonEmpty() || (cases.impliesThatCases != null && cases.impliesThatCases.nonEmpty()))) return true;
        return decl.mods instanceof JmlTree.JmlModifiers jm && !jm.jmlmods.isEmpty();
    }

    /** True if the declaration comes from a .jml file */
    static boolean fromJml(JmlTree.JmlSource decl) {
        JavaFileObject src = decl == null ? null : decl.source();
        return src != null && src.getName().endsWith(".jml");
    }
    
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
        for (String s: files) { // 'files' is null if 'd' is not a valid directory, that is, Main.specs is incorrectly initialized
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
