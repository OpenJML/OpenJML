package org.openjml.lsp.test;

import org.eclipse.lsp4j.Location;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.DefinitionFinder;
import org.openjml.lsp.OpenJMLSettings;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Comprehensive go-to-definition tests covering the four cross-file scenarios:
 *
 * <ol>
 *   <li><b>Java field {@code cField} declared in {@code C.java}</b> — used in Java and JML
 *       text in {@code C.java}, {@code B.java}, {@code A.java} (body asserts only), and
 *       {@code A.jml} (invariants and method specs).</li>
 *
 *   <li><b>JML ghost field {@code cGhostField} declared in {@code C.java}</b> (inline ghost,
 *       no companion {@code .jml}) — used in JML text in the same files as above.</li>
 *
 *   <li><b>Java field {@code aField} declared in {@code A.java}</b>, with a spec stub
 *       {@code public int aField;} also in {@code A.jml} — Find Declaration must navigate
 *       to {@code A.java} (the Java entry takes precedence over the spec stub).</li>
 *
 *   <li><b>Ghost field {@code ghostInAJml} declared only in {@code A.jml}</b> — Find
 *       Declaration must navigate to {@code A.jml} regardless of where the use site is.</li>
 * </ol>
 *
 * <p><b>Note on A.java + A.jml:</b> when a {@code .java} file has a companion {@code .jml},
 * the companion replaces the Java file's method specs for verification and the inline
 * method specs in {@code A.java} are not type-attributed.  Find Declaration on those
 * hidden specs returns null (see {@code s3_aField_inAjava_methodSpec_hidden}).
 *
 * <p><b>Test setup:</b> compiling {@code B.java} with the test directory on the source path
 * causes the compiler to attribute {@code A.java} (and its companion {@code A.jml}) and
 * {@code C.java} in the same IAPI context, so all symbols are shared objects.
 */
public class DefinitionFinderJmlTest {

    private Path testdir;
    private String aUri, aJmlUri, bUri, cUri;
    private String aSrc, aJmlSrc, bSrc, cSrc;
    private Map<String, String> openContent;
    private ASTCache cache;

    @Before
    public void setUp() throws Exception {
        String root = System.getProperty("lsp.testdata");
        assertNotNull("System property lsp.testdata must be set", root);
        testdir = Path.of(root, "testGoToDefinitionJml");
        assertTrue("testGoToDefinitionJml directory must exist", testdir.toFile().isDirectory());

        aSrc    = Files.readString(testdir.resolve("A.java"));
        aJmlSrc = Files.readString(testdir.resolve("A.jml"));
        bSrc    = Files.readString(testdir.resolve("B.java"));
        cSrc    = Files.readString(testdir.resolve("C.java"));

        aUri    = testdir.resolve("A.java").toUri().toString();
        aJmlUri = testdir.resolve("A.jml").toUri().toString();
        bUri    = testdir.resolve("B.java").toUri().toString();
        cUri    = testdir.resolve("C.java").toUri().toString();

        // Compile B.java; A.java, A.jml, and C.java are pulled in via sourcepath.
        // All symbols are attributed in a single IAPI context, ensuring symbol-identity
        // consistency for declaration-index lookups.
        OpenJMLSettings settings = new OpenJMLSettings();
        settings.sourcePath = testdir.toString();
        CheckRunner.checkFile(testdir.resolve("B.java").toString(), bUri, settings);

        openContent = new HashMap<>();
        openContent.put(aUri,    aSrc);
        openContent.put(aJmlUri, aJmlSrc);
        openContent.put(bUri,    bSrc);
        openContent.put(cUri,    cSrc);

        cache = CheckRunner.getASTCache();
    }

    // =======================================================================
    // Scenario 1 — Java field cField declared in C.java
    // =======================================================================

    @Test
    public void s1_cField_inCjava_jmlSpec() {
        // C.java: //@ requires cField >= 0;
        assertDecl(defAt(cUri, cSrc, "requires cField >= 0", "cField"),
                cUri, cSrc, "public int cField");
    }

    @Test
    public void s1_cField_inCjava_javaBody() {
        // C.java: int x = cField;
        assertDecl(defAt(cUri, cSrc, "int x = cField", "cField"),
                cUri, cSrc, "public int cField");
    }

    @Test
    public void s1_cField_inBjava_jmlSpec() {
        // B.java: //@ requires cObj.cField >= 0;
        assertDecl(defAt(bUri, bSrc, "cObj.cField >= 0", "cField"),
                cUri, cSrc, "public int cField");
    }

    @Test
    public void s1_cField_inAjava_jmlBodyAssert() {
        // A.java: //@ assert cObj.cField >= 0;
        assertDecl(defAt(aUri, aSrc, "assert cObj.cField >= 0", "cField"),
                cUri, cSrc, "public int cField");
    }

    @Test
    public void s1_cField_inAjml_invariant() {
        // A.jml: //@ invariant cObj.cField >= 0;
        assertDecl(defAt(aJmlUri, aJmlSrc, "invariant cObj.cField >= 0", "cField"),
                cUri, cSrc, "public int cField");
    }

    @Test
    public void s1_cField_inAjml_methodSpec() {
        // A.jml: //@ requires cObj.cField >= 0;
        assertDecl(defAt(aJmlUri, aJmlSrc, "requires cObj.cField >= 0", "cField"),
                cUri, cSrc, "public int cField");
    }

    // =======================================================================
    // Scenario 2 — JML ghost field cGhostField declared in C.java (no companion .jml)
    // =======================================================================

    @Test
    public void s2_cGhostField_inCjava_jmlSpec() {
        // C.java: //@ requires cGhostField >= 0;
        assertDecl(defAt(cUri, cSrc, "requires cGhostField >= 0", "cGhostField"),
                cUri, cSrc, "ghost public int cGhostField");
    }

    @Test
    public void s2_cGhostField_inBjava_jmlSpec() {
        // B.java: //@ requires cObj.cGhostField >= 0;
        assertDecl(defAt(bUri, bSrc, "cObj.cGhostField >= 0", "cGhostField"),
                cUri, cSrc, "ghost public int cGhostField");
    }

    @Test
    public void s2_cGhostField_inAjava_jmlBodyAssert() {
        // A.java: //@ assert cObj.cGhostField >= 0;
        assertDecl(defAt(aUri, aSrc, "assert cObj.cGhostField >= 0", "cGhostField"),
                cUri, cSrc, "ghost public int cGhostField");
    }

    @Test
    public void s2_cGhostField_inAjml_invariant() {
        // A.jml: //@ invariant cObj.cGhostField >= 0;
        assertDecl(defAt(aJmlUri, aJmlSrc, "invariant cObj.cGhostField >= 0", "cGhostField"),
                cUri, cSrc, "ghost public int cGhostField");
    }

    @Test
    public void s2_cGhostField_inAjml_methodSpec() {
        // A.jml: //@ requires cObj.cGhostField >= 0;
        assertDecl(defAt(aJmlUri, aJmlSrc, "requires cObj.cGhostField >= 0", "cGhostField"),
                cUri, cSrc, "ghost public int cGhostField");
    }

    // =======================================================================
    // Scenario 3 — Java field aField in A.java; spec stub also in A.jml.
    //              Find Declaration always navigates to A.java.
    // =======================================================================

    @Test
    public void s3_aField_inAjava_javaBody() {
        // A.java: int x = aField;
        assertDecl(defAt(aUri, aSrc, "int x = aField", "aField"),
                aUri, aSrc, "public int aField");
    }

    @Test
    public void s3_aField_inAjava_jmlBodyAssert() {
        // A.java: //@ assert aField >= 0;
        assertDecl(defAt(aUri, aSrc, "assert aField >= 0", "aField"),
                aUri, aSrc, "public int aField");
    }

    /**
     * Method spec in A.java — HIDDEN by the companion A.jml file, which replaces
     * all method specs for verification.  The inline spec is not type-attributed,
     * so Find Declaration returns null.
     */
    @Test
    public void s3_aField_inAjava_methodSpec_hidden() {
        // A.java: //@ requires aField >= 0; — not attributed (A.jml companion overrides)
        assertNull("Method spec in A.java hidden by companion A.jml should return null",
                defAt(aUri, aSrc, "requires aField >= 0", "aField"));
    }

    @Test
    public void s3_aField_inAjml_invariant() {
        // A.jml: //@ invariant aField >= 0;  — must navigate to A.java, not A.jml stub
        assertDecl(defAt(aJmlUri, aJmlSrc, "invariant aField >= 0", "aField"),
                aUri, aSrc, "public int aField");
    }

    @Test
    public void s3_aField_inAjml_methodSpec() {
        // A.jml: //@ requires aField >= 0;  — must navigate to A.java, not A.jml stub
        assertDecl(defAt(aJmlUri, aJmlSrc, "requires aField >= 0", "aField"),
                aUri, aSrc, "public int aField");
    }

    @Test
    public void s3_aField_inBjava_jmlSpec() {
        // B.java: //@ requires aObj.aField >= 0;
        assertDecl(defAt(bUri, bSrc, "aObj.aField >= 0", "aField"),
                aUri, aSrc, "public int aField");
    }

    @Test
    public void s3_aField_inBjava_javaBody() {
        // B.java: int y = aObj.aField;
        assertDecl(defAt(bUri, bSrc, "int y = aObj.aField", "aField"),
                aUri, aSrc, "public int aField");
    }

    // =======================================================================
    // Scenario 4 — Ghost field ghostInAJml declared only in A.jml
    //              Find Declaration must always navigate to A.jml
    // =======================================================================

    @Test
    public void s4_ghostInAJml_inAjava_jmlBodyAssert() {
        // A.java: //@ assert ghostInAJml >= 0;
        assertDecl(defAt(aUri, aSrc, "assert ghostInAJml >= 0", "ghostInAJml"),
                aJmlUri, aJmlSrc, "ghost public int ghostInAJml");
    }

    @Test
    public void s4_ghostInAJml_inAjml_invariant() {
        // A.jml: //@ invariant ghostInAJml >= 0;
        assertDecl(defAt(aJmlUri, aJmlSrc, "invariant ghostInAJml >= 0", "ghostInAJml"),
                aJmlUri, aJmlSrc, "ghost public int ghostInAJml");
    }

    @Test
    public void s4_ghostInAJml_inAjml_methodSpec() {
        // A.jml: //@ requires ghostInAJml >= 0;
        assertDecl(defAt(aJmlUri, aJmlSrc, "requires ghostInAJml >= 0", "ghostInAJml"),
                aJmlUri, aJmlSrc, "ghost public int ghostInAJml");
    }

    @Test
    public void s4_ghostInAJml_inBjava_jmlSpec() {
        // B.java: //@ requires aObj.ghostInAJml >= 0;
        assertDecl(defAt(bUri, bSrc, "aObj.ghostInAJml >= 0", "ghostInAJml"),
                aJmlUri, aJmlSrc, "ghost public int ghostInAJml");
    }

    // =======================================================================
    // Helpers
    // =======================================================================

    /** Find the definition of identifier {@code id} at the line containing {@code ctx}. */
    private Location defAt(String uri, String source, String ctx, String id) {
        int lineStart = source.indexOf(ctx);
        assertTrue("Context «" + ctx + "» not found", lineStart >= 0);
        int idPos = source.indexOf(id, lineStart);
        assertTrue("Identifier «" + id + "» not found after context string", idPos >= 0);
        int[] lc = DefinitionFinder.offsetToLineCol(source, idPos);
        return DefinitionFinder.findDefinition(uri, lc[0], lc[1], openContent, cache);
    }

    /** Assert that {@code loc} is non-null, in {@code expectedUri}, at the line containing {@code marker}. */
    private void assertDecl(Location loc, String expectedUri, String expectedSrc, String marker) {
        assertNotNull("Expected non-null location (marker: «" + marker + "»)", loc);
        assertEquals("Wrong file", expectedUri, loc.getUri());
        assertEquals("Wrong declaration line (marker: «" + marker + "»)",
                lineOf(expectedSrc, marker), loc.getRange().getStart().getLine());
    }

    /** Return the 0-indexed line number of the first line containing {@code substr}. */
    private static int lineOf(String source, String substr) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(substr)) return i;
        }
        fail("Not found in source: «" + substr + "»");
        return -1;
    }
}
