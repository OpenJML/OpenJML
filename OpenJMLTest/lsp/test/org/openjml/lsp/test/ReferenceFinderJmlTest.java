package org.openjml.lsp.test;

import org.eclipse.lsp4j.Location;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.DefinitionFinder;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.ReferenceFinder;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * Comprehensive Find References tests covering the same four cross-file
 * scenarios as {@code DefinitionFinderJmlTest}, verifying that every Java
 * and JML use site is returned and that non-attributed sites are excluded.
 *
 * <p><b>Scenarios:</b>
 * <ol>
 *   <li><b>cField</b> — Java field in {@code C.java}; used in C.java JML spec and
 *       Java body, A.java JML body assert, A.jml invariant and method spec, and
 *       B.java JML spec (6 use sites).</li>
 *   <li><b>cGhostField</b> — JML ghost field in {@code C.java}; same set of use files
 *       minus the C.java Java body (5 use sites).</li>
 *   <li><b>aField</b> — Java field in {@code A.java} (spec stub in A.jml); used in
 *       A.java Java body and JML body assert, A.jml invariant and method spec, and
 *       B.java JML spec and Java body (6 use sites).  The hidden inline spec in
 *       A.java must NOT appear.</li>
 *   <li><b>ghostInAJml</b> — ghost field declared only in {@code A.jml}; used in
 *       A.java JML body assert, A.jml invariant and method spec, and B.java JML
 *       spec (4 use sites).</li>
 * </ol>
 *
 * <p>Uses the same test data directory ({@code testGoToDefinitionJml/}) and
 * the same compilation setup (compile {@code B.java} with source path) as
 * {@link DefinitionFinderJmlTest}.
 */
public class ReferenceFinderJmlTest {

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
    //
    // Expected use sites (includeDeclaration=false):
    //   C.java  : //@ requires cField >= 0;             (JML spec)
    //   C.java  : int x = cField;                       (Java body)
    //   A.java  : //@ assert cObj.cField >= 0;          (JML body assert)
    //   A.jml   : //@ invariant cObj.cField >= 0;       (invariant)
    //   A.jml   : //@ requires cObj.cField >= 0;        (method spec)
    //   B.java  : //@ requires cObj.cField >= 0;        (JML spec)
    //   Total: 6
    // =======================================================================

    @Test
    public void s1_cField_refsFromDeclaration_allSixUseSites() {
        List<Location> refs = refsAt(cUri, cSrc, "public int cField", "cField", false);
        assertHasRef(refs, cUri,    cSrc,    "requires cField >= 0");       // C.java JML spec
        assertHasRef(refs, cUri,    cSrc,    "int x = cField");             // C.java Java body
        assertHasRef(refs, aUri,    aSrc,    "assert cObj.cField >= 0");    // A.java JML body assert
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant cObj.cField >= 0"); // A.jml invariant
        assertHasRef(refs, aJmlUri, aJmlSrc, "requires cObj.cField >= 0");  // A.jml method spec
        assertHasRef(refs, bUri,    bSrc,    "requires cObj.cField >= 0");  // B.java JML spec
        assertEquals("cField use count", 6, refs.size());
    }

    @Test
    public void s1_cField_refsFromJavaBody_sameSet() {
        List<Location> refs = refsAt(cUri, cSrc, "int x = cField", "cField", false);
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant cObj.cField >= 0");
        assertHasRef(refs, bUri,    bSrc,    "requires cObj.cField >= 0");
        assertEquals(6, refs.size());
    }

    @Test
    public void s1_cField_refsFromJmlSpec_inBjava() {
        List<Location> refs = refsAt(bUri, bSrc, "requires cObj.cField >= 0", "cField", false);
        assertHasRef(refs, cUri, cSrc, "requires cField >= 0");
        assertHasRef(refs, cUri, cSrc, "int x = cField");
        assertHasRef(refs, aUri, aSrc, "assert cObj.cField >= 0");
        assertEquals(6, refs.size());
    }

    @Test
    public void s1_cField_refsFromAjml_invariant() {
        List<Location> refs = refsAt(aJmlUri, aJmlSrc, "invariant cObj.cField >= 0", "cField", false);
        assertHasRef(refs, cUri,    cSrc,    "int x = cField");
        assertHasRef(refs, aJmlUri, aJmlSrc, "requires cObj.cField >= 0");
        assertHasRef(refs, bUri,    bSrc,    "requires cObj.cField >= 0");
        assertEquals(6, refs.size());
    }

    @Test
    public void s1_cField_refsFromAjml_methodSpec() {
        List<Location> refs = refsAt(aJmlUri, aJmlSrc, "requires cObj.cField >= 0", "cField", false);
        assertHasRef(refs, cUri, cSrc, "requires cField >= 0");
        assertHasRef(refs, aUri, aSrc, "assert cObj.cField >= 0");
        assertEquals(6, refs.size());
    }

    @Test
    public void s1_cField_includeDeclaration_addsSeventhEntry() {
        List<Location> refs = refsAt(cUri, cSrc, "public int cField", "cField", true);
        assertHasRef(refs, cUri, cSrc, "public int cField"); // declaration
        assertEquals(7, refs.size());
    }

    // =======================================================================
    // Scenario 2 — JML ghost field cGhostField declared in C.java (no .jml)
    //
    // Expected use sites (includeDeclaration=false):
    //   C.java  : //@ requires cGhostField >= 0;           (JML spec)
    //   A.java  : //@ assert cObj.cGhostField >= 0;        (JML body assert)
    //   A.jml   : //@ invariant cObj.cGhostField >= 0;     (invariant)
    //   A.jml   : //@ requires cObj.cGhostField >= 0;      (method spec)
    //   B.java  : //@ requires cObj.cGhostField >= 0;      (JML spec)
    //   Total: 5
    // =======================================================================

    @Test
    public void s2_cGhostField_refsFromDeclaration_allFiveUseSites() {
        List<Location> refs = refsAt(cUri, cSrc, "ghost public int cGhostField", "cGhostField", false);
        assertHasRef(refs, cUri,    cSrc,    "requires cGhostField >= 0");       // C.java JML spec
        assertHasRef(refs, aUri,    aSrc,    "assert cObj.cGhostField >= 0");    // A.java JML body assert
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant cObj.cGhostField >= 0"); // A.jml invariant
        assertHasRef(refs, aJmlUri, aJmlSrc, "requires cObj.cGhostField >= 0");  // A.jml method spec
        assertHasRef(refs, bUri,    bSrc,    "requires cObj.cGhostField >= 0");  // B.java JML spec
        assertEquals("cGhostField use count", 5, refs.size());
    }

    @Test
    public void s2_cGhostField_refsFromJmlSpec_inCjava() {
        List<Location> refs = refsAt(cUri, cSrc, "requires cGhostField >= 0", "cGhostField", false);
        assertHasRef(refs, aUri,    aSrc,    "assert cObj.cGhostField >= 0");
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant cObj.cGhostField >= 0");
        assertHasRef(refs, bUri,    bSrc,    "requires cObj.cGhostField >= 0");
        assertEquals(5, refs.size());
    }

    @Test
    public void s2_cGhostField_refsFromAjava_bodyAssert() {
        List<Location> refs = refsAt(aUri, aSrc, "assert cObj.cGhostField >= 0", "cGhostField", false);
        assertHasRef(refs, cUri,    cSrc,    "requires cGhostField >= 0");
        assertHasRef(refs, aJmlUri, aJmlSrc, "requires cObj.cGhostField >= 0");
        assertEquals(5, refs.size());
    }

    @Test
    public void s2_cGhostField_refsFromAjml_methodSpec() {
        List<Location> refs = refsAt(aJmlUri, aJmlSrc, "requires cObj.cGhostField >= 0", "cGhostField", false);
        assertHasRef(refs, cUri, cSrc, "requires cGhostField >= 0");
        assertHasRef(refs, bUri, bSrc, "requires cObj.cGhostField >= 0");
        assertEquals(5, refs.size());
    }

    @Test
    public void s2_cGhostField_includeDeclaration_addsSixthEntry() {
        List<Location> refs = refsAt(cUri, cSrc, "ghost public int cGhostField", "cGhostField", true);
        assertHasRef(refs, cUri, cSrc, "ghost public int cGhostField"); // declaration
        assertEquals(6, refs.size());
    }

    // =======================================================================
    // Scenario 3 — Java field aField in A.java; spec stub also in A.jml
    //
    // Expected use sites (includeDeclaration=false):
    //   A.java  : int x = aField;                 (Java body)
    //   A.java  : //@ assert aField >= 0;          (JML body assert)
    //   A.jml   : //@ invariant aField >= 0;       (invariant)
    //   A.jml   : //@ requires aField >= 0;        (method spec)
    //   B.java  : //@ requires aObj.aField >= 0;   (JML spec — field access)
    //   B.java  : int y = aObj.aField;             (Java body — field access)
    //   Total: 6
    //
    // The hidden //@ requires aField >= 0; in A.java (line 12) must NOT appear.
    // The spec stub  public int aField;  in A.jml (line 9) counts as a
    //   declaration site, not a use site, so it must NOT appear with includeDeclaration=false.
    // =======================================================================

    @Test
    public void s3_aField_refsFromDeclaration_allSixUseSites() {
        List<Location> refs = refsAt(aUri, aSrc, "public int aField = 0", "aField", false);
        assertHasRef(refs, aUri,    aSrc,    "int x = aField");          // A.java Java body
        assertHasRef(refs, aUri,    aSrc,    "assert aField >= 0");      // A.java JML body assert
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant aField >= 0");   // A.jml invariant
        assertHasRef(refs, aJmlUri, aJmlSrc, "requires aField >= 0");    // A.jml method spec
        assertHasRef(refs, bUri,    bSrc,    "aObj.aField >= 0");        // B.java JML spec
        assertHasRef(refs, bUri,    bSrc,    "int y = aObj.aField");     // B.java Java body
        assertEquals("aField use count", 6, refs.size());
    }

    @Test
    public void s3_aField_refsFromJavaBody() {
        List<Location> refs = refsAt(aUri, aSrc, "int x = aField", "aField", false);
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant aField >= 0");
        assertHasRef(refs, bUri,    bSrc,    "int y = aObj.aField");
        assertEquals(6, refs.size());
    }

    @Test
    public void s3_aField_refsFromJmlBodyAssert_inAjava() {
        List<Location> refs = refsAt(aUri, aSrc, "assert aField >= 0", "aField", false);
        assertHasRef(refs, aJmlUri, aJmlSrc, "requires aField >= 0");
        assertHasRef(refs, bUri,    bSrc,    "aObj.aField >= 0");
        assertEquals(6, refs.size());
    }

    @Test
    public void s3_aField_refsFromAjml_invariant() {
        List<Location> refs = refsAt(aJmlUri, aJmlSrc, "invariant aField >= 0", "aField", false);
        assertHasRef(refs, aUri, aSrc, "int x = aField");
        assertHasRef(refs, aUri, aSrc, "assert aField >= 0");
        assertHasRef(refs, bUri, bSrc, "int y = aObj.aField");
        assertEquals(6, refs.size());
    }

    @Test
    public void s3_aField_refsFromBjava_fieldAccessInSpec() {
        List<Location> refs = refsAt(bUri, bSrc, "aObj.aField >= 0", "aField", false);
        assertHasRef(refs, aUri,    aSrc,    "int x = aField");
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant aField >= 0");
        assertHasRef(refs, bUri,    bSrc,    "int y = aObj.aField");
        assertEquals(6, refs.size());
    }

    @Test
    public void s3_aField_refsFromBjava_fieldAccessInJavaBody() {
        List<Location> refs = refsAt(bUri, bSrc, "int y = aObj.aField", "aField", false);
        assertHasRef(refs, aUri,    aSrc,    "assert aField >= 0");
        assertHasRef(refs, aJmlUri, aJmlSrc, "requires aField >= 0");
        assertEquals(6, refs.size());
    }

    @Test
    public void s3_aField_hiddenMethodSpec_notInRefs() {
        // A.java //@ requires aField >= 0; (line 12) is HIDDEN by the A.jml companion.
        // It is not type-attributed so its symbol is null — must not appear in refs.
        List<Location> refs = refsAt(aUri, aSrc, "public int aField = 0", "aField", false);
        int hiddenLine = lineOf(aSrc, "aField in A.java method spec (HIDDEN");
        boolean hiddenPresent = refs.stream().anyMatch(loc ->
                aUri.equals(loc.getUri()) && hiddenLine == loc.getRange().getStart().getLine());
        assertFalse("Hidden A.java method spec must not appear in refs", hiddenPresent);
    }

    @Test
    public void s3_aField_specStub_notInRefsWithoutIncludeDeclaration() {
        // A.jml line 9: public int aField; is a spec stub (declaration site).
        // With includeDeclaration=false it must not appear.
        List<Location> refs = refsAt(aUri, aSrc, "public int aField = 0", "aField", false);
        int stubLine = lineOf(aJmlSrc, "spec stub");
        boolean stubPresent = refs.stream().anyMatch(loc ->
                aJmlUri.equals(loc.getUri()) && stubLine == loc.getRange().getStart().getLine());
        assertFalse("A.jml spec stub must not appear when includeDeclaration=false", stubPresent);
    }

    @Test
    public void s3_aField_includeDeclaration_includesJavaDecl() {
        List<Location> refs = refsAt(aUri, aSrc, "public int aField = 0", "aField", true);
        assertHasRef(refs, aUri, aSrc, "public int aField = 0"); // Java declaration
        assertTrue("aField total refs with decl should be >= 7", refs.size() >= 7);
    }

    // =======================================================================
    // Scenario 4 — Ghost field ghostInAJml declared only in A.jml
    //
    // Expected use sites (includeDeclaration=false):
    //   A.java  : //@ assert ghostInAJml >= 0;         (JML body assert)
    //   A.jml   : //@ invariant ghostInAJml >= 0;      (invariant)
    //   A.jml   : //@ requires ghostInAJml >= 0;       (method spec)
    //   B.java  : //@ requires aObj.ghostInAJml >= 0;  (JML spec — field access)
    //   Total: 4
    // =======================================================================

    @Test
    public void s4_ghostInAJml_refsFromDeclaration_allFourUseSites() {
        List<Location> refs = refsAt(aJmlUri, aJmlSrc, "ghost public int ghostInAJml", "ghostInAJml", false);
        assertHasRef(refs, aUri,    aSrc,    "assert ghostInAJml >= 0");          // A.java JML body assert
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant ghostInAJml >= 0");       // A.jml invariant
        assertHasRef(refs, aJmlUri, aJmlSrc, "requires ghostInAJml >= 0");        // A.jml method spec
        assertHasRef(refs, bUri,    bSrc,    "aObj.ghostInAJml >= 0");            // B.java JML spec
        assertEquals("ghostInAJml use count", 4, refs.size());
    }

    @Test
    public void s4_ghostInAJml_refsFromAjava_bodyAssert() {
        List<Location> refs = refsAt(aUri, aSrc, "assert ghostInAJml >= 0", "ghostInAJml", false);
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant ghostInAJml >= 0");
        assertHasRef(refs, aJmlUri, aJmlSrc, "requires ghostInAJml >= 0");
        assertHasRef(refs, bUri,    bSrc,    "aObj.ghostInAJml >= 0");
        assertEquals(4, refs.size());
    }

    @Test
    public void s4_ghostInAJml_refsFromAjml_invariant() {
        List<Location> refs = refsAt(aJmlUri, aJmlSrc, "invariant ghostInAJml >= 0", "ghostInAJml", false);
        assertHasRef(refs, aUri, aSrc, "assert ghostInAJml >= 0");
        assertHasRef(refs, bUri, bSrc, "aObj.ghostInAJml >= 0");
        assertEquals(4, refs.size());
    }

    @Test
    public void s4_ghostInAJml_refsFromAjml_methodSpec() {
        List<Location> refs = refsAt(aJmlUri, aJmlSrc, "requires ghostInAJml >= 0", "ghostInAJml", false);
        assertHasRef(refs, aUri,    aSrc,    "assert ghostInAJml >= 0");
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant ghostInAJml >= 0");
        assertHasRef(refs, bUri,    bSrc,    "aObj.ghostInAJml >= 0");
        assertEquals(4, refs.size());
    }

    @Test
    public void s4_ghostInAJml_refsFromBjava_fieldAccess() {
        List<Location> refs = refsAt(bUri, bSrc, "aObj.ghostInAJml >= 0", "ghostInAJml", false);
        assertHasRef(refs, aUri,    aSrc,    "assert ghostInAJml >= 0");
        assertHasRef(refs, aJmlUri, aJmlSrc, "invariant ghostInAJml >= 0");
        assertEquals(4, refs.size());
    }

    @Test
    public void s4_ghostInAJml_includeDeclaration_addsFifthEntry() {
        List<Location> refs = refsAt(aJmlUri, aJmlSrc, "ghost public int ghostInAJml", "ghostInAJml", true);
        assertHasRef(refs, aJmlUri, aJmlSrc, "ghost public int ghostInAJml"); // declaration
        assertEquals(5, refs.size());
    }

    // =======================================================================
    // Helpers
    // =======================================================================

    /**
     * Find references of identifier {@code id} at the position following {@code ctx}
     * in {@code source} (for {@code uri}).
     */
    private List<Location> refsAt(String uri, String source, String ctx, String id,
                                   boolean includeDecl) {
        int lineStart = source.indexOf(ctx);
        assertTrue("Context «" + ctx + "» not found", lineStart >= 0);
        int idPos = source.indexOf(id, lineStart);
        assertTrue("Identifier «" + id + "» not found after context", idPos >= 0);
        int[] lc = DefinitionFinder.offsetToLineCol(source, idPos);
        return ReferenceFinder.findReferences(uri, lc[0], lc[1], openContent, cache, includeDecl);
    }

    /**
     * Assert that {@code refs} contains at least one location in {@code expectedUri}
     * on the line containing {@code marker} in {@code expectedSrc}.
     */
    private void assertHasRef(List<Location> refs, String expectedUri,
                               String expectedSrc, String marker) {
        int expectedLine = lineOf(expectedSrc, marker);
        boolean found = refs.stream().anyMatch(loc ->
                expectedUri.equals(loc.getUri()) &&
                expectedLine == loc.getRange().getStart().getLine());
        assertTrue("Expected ref in " + new File(expectedUri).getName() +
                " at line containing «" + marker + "» (1-indexed line " + (expectedLine + 1) + ")" +
                "\nActual refs: " + summarize(refs), found);
    }

    /** Return the 0-indexed line number of the first line in {@code source} containing {@code substr}. */
    private static int lineOf(String source, String substr) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(substr)) return i;
        }
        fail("Not found in source: «" + substr + "»");
        return -1;
    }

    private String summarize(List<Location> refs) {
        return refs.stream()
                .map(loc -> new File(loc.getUri()).getName() + ":"
                        + (loc.getRange().getStart().getLine() + 1))
                .sorted()
                .collect(Collectors.joining(", "));
    }
}
