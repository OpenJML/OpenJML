package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjmltest.EscBaseFiles;
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
 * lists, one per line, the public and protected methods known to have no specification (none, if absent).
 * An optional 'options' file gives extra ESC options, one per line (e.g. a --method selection for a large class).
 * Implementation-level annotations (loop invariants etc.) belong in the java.base source itself.
 *
 * The source file is checked in place, as part of java.base, by patching java.base with the file's own package
 * folder. javac reads a patch folder as a source path for the module, so patching with the whole source tree
 * would compile every java.base source the class refers to; from the package folder, implicit lookups
 * (folder/java/lang/X.java) find nothing and all other classes come from the built JDK.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class SpecsVerify extends EscBaseFiles {

    /** The subfolder of OpenJMLTest that holds the data for this suite */
    public static final String testdir = "testspecs-verify";

    /** Serialization hooks, which are called only by the serialization machinery; they are not verified
     * until the java.io serialization classes are specified */
    public static final String serializationMethods = "readObject,writeObject,readObjectNoData,readResolve,writeReplace";

    /** The java.base sources, relative to OpenJMLTest */
    public static final String javaBase = "../OpenJMLsrc/src/java.base/share/classes";

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

    String className() {
        return foldername.replace('-', '.');
    }

    /** The class's java.base source file */
    String sourceFile() {
        String file = javaBase + "/" + className().replace('.', '/') + ".java";
        assertTrue("No java.base source for " + className() + ": " + file, new File(file).isFile());
        return file;
    }

    /** The option that makes the source file part of java.base */
    String patchOption() {
        return "--patch-module=java.base=" + new File(sourceFile()).getParent();
    }

    /** ESC of the implementation against its specs */
    @Test
    public void testVerify() throws Exception {
        var args = new ArrayList<String>(java.util.List.of(patchOption(), "--check-feasibility=return",
                "--exclude=" + serializationMethods));
        Path options = Path.of(outDir(), "options");
        if (Files.exists(options)) {
            for (String line: Files.readAllLines(options)) if (!line.isBlank()) args.add(line.trim());
        }
        escOnFiles(sourceFile(), outDir(), args.toArray(new String[0]));
    }

    /** Every public and protected method and constructor of the class, other than those listed in 'unspecified',
     * has a specification case in its .jml file */
    @Test
    public void testMethodsSpecified() throws Exception {
        StringWriter sw = new StringWriter();
        var main = new org.jmlspecs.openjml.Main("openjml", new PrintWriter(sw, true));
        Context ctx = main.initialize(null);
        int ex = main.compile(new String[]{ "--check", patchOption(), sourceFile() }, ctx).exitCode;
        assertEquals("Type-checking failed:\n" + sw, 0, ex);

        Symtab syms = Symtab.instance(ctx);
        ClassSymbol csym = syms.getClass(syms.java_base, Names.instance(ctx).fromString(className()));
        assertTrue("Class not found: " + className(), csym != null);
        JmlSpecs specs = JmlSpecs.instance(ctx);
        java.util.List<String> missing = new ArrayList<>();
        int count = 0;
        for (Symbol s: csym.members().getSymbols()) {
            if (!(s instanceof MethodSymbol msym)) continue;
            if ((msym.flags() & (Flags.PUBLIC|Flags.PROTECTED)) == 0 || (msym.flags() & (Flags.SYNTHETIC|Flags.BRIDGE)) != 0) continue;
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
        assertEquals("Public and protected methods of " + className() + " without specifications", expected, missing);
    }
}
