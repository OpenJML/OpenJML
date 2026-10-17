package org.jmlspecs.openjmltest.testsuites;

import org.jmlspecs.openjmltest.TCBase;
import org.jmlspecs.openjml.Main;

import java.io.File;
import java.lang.reflect.Modifier;
import java.nio.file.Files;
import java.util.*;

import javax.tools.JavaFileObject;

import static org.junit.Assert.*;
import org.junit.*;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.MockJavaFileObject;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.util.Log;

/** This test suite checks that the library specifications compile under --rac, one test per package:
 * for each package with specification (.jml) files, it compiles with openjml --rac a temporary .java file
 * that declares a field of each public class of that package that has a specification file, and expects
 * no errors. SpecsBase does the corresponding check for --check, one class at a time.
 *
 * A specification can type check but fail to compile under --rac, for example when a clause uses a model
 * field that is declared only for ESC (//-RAC@), such as Iterable's values (#1012). Compiling a package
 * also compiles the specifications its classes depend on, so an error may be reported in a .jml file of
 * another package; the error message names that file.
 *
 * The classes are those found by SpecsBase.findAllFiles(), with the same exclusions. Warnings are not
 * failures. This suite only compiles: it does not run RAC code (which could find, for instance, clauses
 * that read private fields of a library class).
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SpecsRacCompile extends TCBase {

    /** The test parameters: the packages that have specification files */
    @Parameters
    static public Collection<String[]> datax() {
        Collection<String[]> data = new ArrayList<String[]>();
        for (String pkg: classesByPackage().keySet()) data.add(new String[]{ pkg });
        return data;
    }

    /** The classes that have specification files, grouped by package */
    static Map<String,List<String>> classesByPackage() {
        Map<String,List<String>> map = new TreeMap<>();
        for (String c: SpecsBase.findAllFiles()) {
            int p = c.lastIndexOf('.');
            if (p < 0) continue;
            map.computeIfAbsent(c.substring(0,p), k -> new ArrayList<>()).add(c);
        }
        return map;
    }

    /** The package tested by this instance of the test */
    /*@ non_null*/
    private String pkg;

    public SpecsRacCompile(String pkg) {
        this.pkg = pkg;
    }

    @Override @Before
    public void setUp() throws Exception {
        ignoreNotes = true;
        super.setUp();
        assertTrue("Specifications folder does not exist: " + Main.specs, new File(Main.specs).exists());
    }

    /** Needs as many entries as the most type arguments that will be found */
    static String[] typeargs = { "", "<?>", "<?,?>", "<?,?,?>", "<?,?,?,?>", "<?,?,?,?,?>" };

    @Test
    public void test() throws Exception {
        StringBuilder program = new StringBuilder("public class AJDK {\n");
        int n = 0;
        for (String className: classesByPackage().get(pkg)) {
            Class<?> clazz;
            try {
                clazz = Class.forName(className);
            } catch (ClassNotFoundException e) {
                continue; // a specification file without a class; SpecsBase reports it
            }
            if (!Modifier.isPublic(clazz.getModifiers())) continue;
            program.append("  " + className + typeargs[clazz.getTypeParameters().length] + " f" + (++n) + ";\n");
        }
        program.append("}\n");
        Assume.assumeTrue("No public classes in " + pkg, n > 0);

        JavaFileObject f = new MockJavaFileObject("AJDK.java", program.toString());
        addMockFile("#B/AJDK.java", f);
        Log.instance(context).useSource(f);
        mockFiles.addMockByUri(f.toUri().normalize(), f);
        File outdir = Files.createTempDirectory("specsraccompile").toFile();
        try {
            main.compile(new String[]{ "--rac", "-d", outdir.getPath(), f.getName() }, mockFiles);
        } finally {
            for (File ff: outdir.listFiles()) ff.delete();
            outdir.delete();
        }
        String errors = collector.getDiagnostics().stream().map(Object::toString)
                .filter(d -> d.contains("error:")).reduce("", (a,b) -> a + b + "\n");
        if (!errors.isEmpty()) {
            this.out.println(errors);
            fail("Errors compiling the specifications of " + pkg + " under --rac");
        }
    }
}
