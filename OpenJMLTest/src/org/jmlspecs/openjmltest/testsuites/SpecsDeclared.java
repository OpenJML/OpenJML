package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.TCBase;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.MockJavaFileObject;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.util.Names;

/** For each library class with a .jml file (the classes SpecsBase checks), checks that the .jml declares every
 * public and protected field, method and constructor that the class itself (not a supertype) declares, as the
 * binary class has them (#1099). A member counts as declared when its specs come from the .jml, the same notion as
 * the jml.undeclared.member warning (JmlAttr.warnUndeclaredMember, #1060). Synthetic and bridge members are skipped,
 * as are implicit ones that javac generates and the class file does not mark (default constructors, enum
 * values()/valueOf), which therefore count like any other member. A public or protected member class is checked the
 * same way, recursively, if the .jml declares it; otherwise only the class itself is reported.
 *
 * The file testspecs-declared/[class, with '.' replaced by '-'] lists the members known to be undeclared, one per
 * line (sorted; nested members prefixed by their class's path, nested classes by 'class '); an absent file means the
 * .jml must be complete. On a mismatch the actual list is written to the same name with suffix '-actual'.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SpecsDeclared extends TCBase {

    /** The subfolder of OpenJMLTest that holds the known-undeclared lists */
    public static final String testdir = "testspecs-declared";

    @Parameters
    static public Collection<String[]> datax() {
        var data = new ArrayList<String[]>();
        for (String c: SpecsBase.findAllFiles()) data.add(new String[]{ c });
        return data;
    }

    /** The fully qualified name of the class under test */
    private String classname;

    public SpecsDeclared(String classname) {
        this.classname = classname;
    }

    @BeforeClass
    public static void clean() {
        var ts = new File(testdir);
        if (ts.exists()) {
            for (var f : ts.listFiles((ff,nm)->nm.endsWith("-actual"))) f.delete();
        }
    }

    @Override @Before
    public void setUp() throws Exception {
        super.setUp();
        expectedExit = -1;
    }

    @Test
    public void testDeclarations() throws Exception {
        // Loads the class and its specs by type-checking a use of it; SpecsBase checks the diagnostics
        int numTypeArgs = Class.forName(classname).getTypeParameters().length;
        String program = "public class AJDK { " + classname + typeargs[numTypeArgs] + " o; }";
        if (classname.equals("org.jmlspecs.lang.internal.datagroup")) program = "public class AJDK { /*@ model public \\datagroup d; */ }";
        JavaFileObject f = new MockJavaFileObject("AJDK.java", program);
        addMockFile("#B/AJDK.java", f);
        mockFiles.addMockByUri(f.toUri().normalize(), f);
        main.compile(new String[]{ f.getName() }, mockFiles);

        ClassSymbol csym = null;
        for (var c: Symtab.instance(context).getClassesForName(Names.instance(context).fromString(classname))) csym = c;
        if (csym == null) fail("Class not found: " + classname);
        JmlSpecs specs = JmlSpecs.instance(context);
        assertTrue("No .jml specs loaded for " + classname, fromJml(specs.getLoadedSpecs(csym).specDecl));
        var missing = new ArrayList<String>();
        collectUndeclared(specs, csym, "", missing);
        missing.sort(null);

        String name = classname.replace('.', '-');
        Path known = Path.of(testdir, name);
        Path actual = Path.of(testdir, name + "-actual");
        var expected = new ArrayList<String>();
        if (Files.exists(known)) {
            for (String line: Files.readAllLines(known)) if (!line.isBlank()) expected.add(line.trim());
        }
        expected.sort(null);
        if (!expected.equals(missing)) {
            Files.createDirectories(Path.of(testdir));
            Files.write(actual, missing);
        }
        assertEquals("Public and protected members of " + classname + " not declared in its .jml", expected, missing);
    }

    /** Adds to 'missing' the public and protected members of csym that its .jml does not declare, each prefixed by
     * 'prefix' (the path of a nested class) */
    void collectUndeclared(JmlSpecs specs, ClassSymbol csym, String prefix, java.util.List<String> missing) {
        for (Symbol s: csym.members().getSymbols()) {
            long flags = s.flags();
            if ((flags & (Flags.PUBLIC|Flags.PROTECTED)) == 0 || (flags & (Flags.SYNTHETIC|Flags.BRIDGE)) != 0) continue;
            if (Utils.isJML(flags)) continue; // declared only in the .jml (model and ghost members)
            if (s instanceof MethodSymbol m) {
                var ms = specs.getLoadedSpecs(m);
                if (ms == null || !fromJml(ms.specDecl)) missing.add(prefix + m);
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

    /** True if the declaration comes from a .jml file */
    static boolean fromJml(org.jmlspecs.openjml.JmlTree.JmlSource decl) {
        JavaFileObject src = decl == null ? null : decl.source();
        return src != null && src.getName().endsWith(".jml");
    }

    /** Needs as many entries as the most type arguments that will be found */
    static final String[] typeargs = { "", "<?>", "<?,?>", "<?,?,?>", "<?,?,?,?>", "<?,?,?,?,?>" };
}
