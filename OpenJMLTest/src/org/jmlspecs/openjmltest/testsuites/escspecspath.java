package org.jmlspecs.openjmltest.testsuites;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;

import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjmltest.EscBaseFiles;

import org.junit.*;
import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** Which specification file OpenJML uses for a class, for combinations of --specs-path,
 * --source-path, -cp, sibling .jml files and binary-only classes.
 * <P>
 * These are the scenarios of the script test test/specspath/run (runscripts2.specspath), run
 * in-process as file tests (which avoids starting a JVM for each one). The sources are those of
 * test/specspath; each scenario's expected output is in test/escspecspath/(scenario name).
 * <P>
 * The script's P5 (the specs path defaulting to the current directory) is not here: an in-process
 * test always runs in OpenJMLTest.
 */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escspecspath extends EscBaseFiles {

    static final String SRC = "test/specspath/";
    static final String OUT = "test/escspecspath/";
    static final String PS = java.io.File.pathSeparator;

    /** The C and Z scenarios reference class C as a .class file, some with a sibling .java file, and javac
     * uses the newer of the two. Each row: the source to compile, then the folders that get its C.class
     * (the first is the source's own). The class files are not committed but built here (#1149). */
    static final String[][] classFiles = {
        { "srct/C.java", "srct", "srctt", "srcta", "srctq" },
        { "srcz/z/C.java", "srcz/z", "srczz/z", "srcza/z" } };

    static boolean classFilesBuilt = false;

    /** Whether the class file is missing or not newer than the given file (if that exists). */
    static boolean stale(File classFile, File other) {
        return !classFile.exists() || (other.exists() && classFile.lastModified() <= other.lastModified());
    }

    /** Compiles each C.class that is missing or not newer than its source, and copies it to each folder
     * whose C.class is missing or not newer than the compiled one or than that folder's own C.java. */
    static synchronized void buildClassFiles() throws Exception {
        if (classFilesBuilt) return;
        for (String[] row: classFiles) {
            File source = new File(SRC + row[0]);
            File compiled = new File(SRC + row[1] + "/C.class");
            if (stale(compiled, source)) {
                StringWriter sw = new StringWriter();
                int ex = Main.execute(new PrintWriter(sw), "-cp", SRC, "--compile", source.getPath());
                if (ex != 0 || stale(compiled, source)) Assert.fail("Compiling " + source + " failed:\n" + sw);
            }
            for (int i = 2; i < row.length; i++) {
                File copy = new File(SRC + row[i] + "/C.class");
                if (stale(copy, compiled) || stale(copy, new File(SRC + row[i] + "/C.java"))) {
                    copy.getParentFile().mkdirs();  // srctt and srczz hold only the class file, so git has no folder
                    Files.copy(compiled.toPath(), copy.toPath(), StandardCopyOption.REPLACE_EXISTING);
                }
            }
        }
        classFilesBuilt = true;
    }

    @Override
    public void setUp() throws Exception {
        super.setUp();
        ignoreNotes = true;
        buildClassFiles();
    }

    /** Runs ESC on the given file of test/specspath, with the given options. Like the script (which runs
     * 'openjml -cp . ...' in test/specspath), every scenario has '-cp test/specspath' first; the C and Z
     * scenarios then add their own -cp, as the script does. */
    void check(String file, String... opts) {
        escOnFiles(SRC + file, OUT + getTestName(), opts);
    }

    // P.java with no specs at all
    @Test public void P1() { check("ppsrc/P.java", "-cp", SRC, "--specs-path", SRC + "specsempty"); }

    // P.java with specs on the specs path: uses ppspecs/P.jml
    @Test public void P2() { check("ppsrc/P.java", "-cp", SRC, "--specs-path", SRC + "ppspecs"); }

    // P.java with sibling specs and nothing on the specs path: uses pxsrc/P.jml
    @Test public void P3() { check("pxsrc/P.java", "-cp", SRC, "--specs-path", SRC + "specsempty"); }

    // P.java with sibling specs and specs on the specs path: uses ppspecs/P.jml
    @Test public void P4() { check("pxsrc/P.java", "-cp", SRC, "--specs-path", SRC + "ppspecs"); }

    // P.java with .jml files in two specs-path folders: uses the first, ppspecs/P.jml
    @Test public void P6() { check("ppsrc/P.java", "-cp", SRC, "--specs-path", SRC + "ppspecs" + PS + SRC); }

    // P.java with .jml files in two specs-path folders: uses the first, ./P.jml
    @Test public void P7() { check("ppsrc/P.java", "-cp", SRC, "--specs-path", SRC + PS + SRC + "ppspecs"); }

    // B.java with no specs: uses bbsrc/B.java
    @Test public void B1() { check("AB.java", "-cp", SRC, "--source-path", SRC + "bbsrc", "--specs-path", SRC + "specsempty"); }

    // B.java with specs on the specs path: uses bbspecs/B.jml
    @Test public void B2() { check("AB.java", "-cp", SRC, "--source-path", SRC + "bbsrc", "--specs-path", SRC + "bbspecs"); }

    // B.java with no specs on the specs path, but sibling specs: uses bxsrc/B.jml
    @Test public void B3() { check("AB.java", "-cp", SRC, "--source-path", SRC + "bxsrc", "--specs-path", SRC + "specsempty"); }

    // B.java with specs on the specs path and sibling specs: uses bbspecs/B.jml
    @Test public void B4() { check("AB.java", "-cp", SRC, "--source-path", SRC + "bxsrc", "--specs-path", SRC + "bbspecs"); }

    // B.java with the specs path defaulting to the source path: uses bxsrc/B.jml
    @Test public void B5() { check("AB.java", "-cp", SRC, "--source-path", SRC + "bxsrc"); }

    // Referenced binary class with .class, .java and .jml: uses ccspecs/C.jml
    @Test public void C1() { check("AC.java", "-cp", SRC, "-cp", SRC + "srct", "--specs-path=" + SRC + "ccspecs"); }

    // Referenced binary class with .class and .java: uses no specs for C (empty specs path) and fails
    @Test public void C2() { check("AC.java", "-cp", SRC, "-cp", SRC + "srct", "--specs-path=" + SRC + "specsempty"); }

    // Referenced binary class with .class and .java: uses no specs for C (the specs path defaults to srct,
    // which has no C.jml) and fails
    @Test public void C3() { check("AC.java", "-cp", SRC, "-cp", SRC + "srct"); }

    // Referenced binary class with .class, .java and .jml: uses srcta/C.jml (the specs path defaults to srcta)
    // and succeeds
    @Test public void C3a() { check("AC.java", "-cp", SRC, "-cp", SRC + "srcta"); }

    // Referenced binary class with only a .class file: an assignable verification failure
    @Test public void C4() { check("AC.java", "-cp", SRC, "-cp", SRC + "srctt", "--specs-path=" + SRC + "specsempty"); }

    // Referenced binary class with .class and a .jml whose package declaration (q) disagrees with its location:
    // a mismatched-package error, and no specs for C
    @Test public void C5() { check("AC.java", "-cp", SRC, "-cp", SRC + "srctq"); }

    // Empty specs path, two .java files on the source path, the second one on the command line:
    // finds the .jml next to the .java file used (pxsrc/P.jml)
    @Test public void Y1() { check("pxsrc/P.java", "-cp", SRC, "--source-path=" + SRC + "ppsrc" + PS + SRC + "pxsrc", "--specs-path=" + SRC + "specsempty"); }

    // Empty specs path, two .java files on the source path, the second one on the command line:
    // uses the command-line .java file (ppsrc/P.java) even though there is a .jml on the source path
    @Test public void Y2() { check("ppsrc/P.java", "-cp", SRC, "--source-path=" + SRC + "pxsrc" + PS + SRC + "ppsrc", "--specs-path=" + SRC + "specsempty"); }

    // Referenced binary class (in package z) with .class, .java and .jml: uses ccspecs/z/C.jml
    @Test public void Z1() { check("AZC.java", "-cp", SRC, "-cp", SRC + "srcz", "--specs-path=" + SRC + "ccspecs"); }

    // Referenced binary class with .class and .java: uses no specs for C (empty specs path) and fails
    @Test public void Z2() { check("AZC.java", "-cp", SRC, "-cp", SRC + "srcz", "--specs-path=" + SRC + "specsempty"); }

    // Referenced binary class with .class and .java: uses no specs for C (the specs path defaults to srcz,
    // which has no z/C.jml) and fails
    @Test public void Z3() { check("AZC.java", "-cp", SRC, "-cp", SRC + "srcz"); }

    // Referenced binary class with .class, .java and .jml: uses srcza/z/C.jml (the specs path defaults to
    // srcza) and succeeds
    @Test public void Z3a() { check("AZC.java", "-cp", SRC, "-cp", SRC + "srcza"); }

    // Referenced binary class with only a .class file: an assignable problem
    @Test public void Z4() { check("AZC.java", "-cp", SRC, "-cp", SRC + "srczz", "--specs-path=" + SRC + "specsempty"); }

    // Referenced binary class with .jml files in two specs-path folders: uses the first, ccspecs/z/C.jml
    @Test public void Z5() { check("AZC.java", "-cp", SRC, "-cp", SRC + "srcza", "--specs-path=" + SRC + "ccspecs" + PS + SRC + "srcza"); }

    // Referenced binary class with .jml files in two specs-path folders: uses the first, srcza/z/C.jml, and succeeds
    @Test public void Z6() { check("AZC.java", "-cp", SRC, "-cp", SRC + "srcza", "--specs-path=" + SRC + "srcza" + PS + SRC + "ccspecs"); }
}
