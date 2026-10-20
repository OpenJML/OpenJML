package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collection;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.jmlspecs.openjmltest.JmlTestSuite;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Names;

/** Verifies JDK library implementations (the java.base sources in OpenJMLsrc, which are what OpenJML's JDK is
 * built from) against their specifications in Specs. Each subfolder of OpenJMLTest/testspecs-verify names one
 * class, with '.' replaced by '-'; its 'expected' file is the golden ESC output, and an optional 'unspecified' file
 * lists, one per line, the public methods known to have no specification (none, if absent).
 * Implementation-level annotations (loop invariants etc.) belong in the java.base source itself.
 *
 * For each class, the source is copied into the folder's 'actual-patch' subfolder (git-ignored) and checked
 * with --patch-module=java.base. Patching from the source tree itself does not work: it holds module-info.java.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SpecsVerify extends EscBaseFiles {

    /** The subfolder of OpenJMLTest that holds the data for this suite */
    public static final String testdir = "testspecs-verify";

    /** The java.base sources */
    public static final String javaBase = JmlTestSuite.repo + "/OpenJMLsrc/src/java.base/share/classes";

    @Parameters
    static public Collection<String[]> datax() {
        ArrayList<String[]> data = new ArrayList<String[]>();
        for (File f: new File(testdir).listFiles()) { // Presumes working directory is OpenJMLTest
            if (f.isDirectory()) data.add(new String[]{ f.getName() });
        }
        data.sort((t1,t2)->t1[0].compareTo(t2[0]));
        return data;
    }

    /** The folder for the class under test, named as the class with '.' replaced by '-' */
    /*@ non_null*/
    private String foldername;

    public SpecsVerify(String foldername) {
        super("", null);
        this.foldername = foldername;
    }

    @Override @org.junit.Before
    public void setUp() throws Exception {
        super.setUp();
        expectedExit = -1;
    }

    String outDir() {
        return testdir + "/" + foldername;
    }

    String patchDir() {
        return outDir() + "/actual-patch";
    }

    String className() {
        return foldername.replace('-', '.');
    }

    /** Copies the class's java.base source into the patch folder; returns the copy's path */
    String preparePatch() throws java.io.IOException {
        String rel = className().replace('.', '/') + ".java";
        Path src = Path.of(javaBase, rel);
        assertTrue("No java.base source for " + className() + ": " + src, Files.isRegularFile(src));
        Path dest = Path.of(patchDir(), rel);
        Files.createDirectories(dest.getParent());
        Files.copy(src, dest, StandardCopyOption.REPLACE_EXISTING);
        return dest.toString();
    }

    /** ESC of the implementation against its specs */
    @Test
    public void testVerify() throws Exception {
        String file = preparePatch();
        escOnFiles(file, outDir(), "--patch-module=java.base=" + patchDir(), "--check-feasibility=return");
    }

    /** Every public method and constructor of the class, other than those listed in 'unspecified',
     * has a specification case in its .jml file */
    @Test
    public void testPublicMethodsSpecified() throws Exception {
        String file = preparePatch();
        StringWriter sw = new StringWriter();
        var main = new org.jmlspecs.openjml.Main("openjml", new PrintWriter(sw, true));
        Context ctx = main.initialize(null);
        int ex = main.compile(new String[]{ "--check", "--patch-module=java.base=" + patchDir(), file }, ctx).exitCode;
        assertEquals("Type-checking failed:\n" + sw, 0, ex);

        Symtab syms = Symtab.instance(ctx);
        ClassSymbol csym = syms.getClass(syms.java_base, Names.instance(ctx).fromString(className()));
        assertTrue("Class not found: " + className(), csym != null);
        JmlSpecs specs = JmlSpecs.instance(ctx);
        java.util.List<String> missing = new ArrayList<>();
        int count = 0;
        for (Symbol s: csym.members().getSymbols()) {
            if (!(s instanceof MethodSymbol msym)) continue;
            if ((msym.flags() & Flags.PUBLIC) == 0 || (msym.flags() & (Flags.SYNTHETIC|Flags.BRIDGE)) != 0) continue;
            count++;
            var ms = specs.getLoadedSpecs(msym);
            boolean specified = ms != null && ms.specDecl != null && ms.specDecl.sourcefile != null
                    && ms.specDecl.sourcefile.getName().endsWith(".jml")
                    && ms.cases != null && ms.cases.cases.nonEmpty();
            if (!specified) missing.add(msym.toString());
        }
        assertTrue("No public methods found in " + className(), count > 0);
        missing.sort(null);
        Path known = Path.of(outDir(), "unspecified");
        var expected = new ArrayList<String>();
        if (Files.exists(known)) {
            for (String line: Files.readAllLines(known)) if (!line.isBlank()) expected.add(line.trim());
        }
        expected.sort(null);
        assertEquals("Public methods of " + className() + " without specifications", expected, missing);
    }
}
