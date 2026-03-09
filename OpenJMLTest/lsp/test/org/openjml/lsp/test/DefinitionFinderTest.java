package org.openjml.lsp.test;

import org.eclipse.lsp4j.Location;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.DefinitionFinder;
import org.openjml.lsp.OpenJMLSettings;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Tests for {@link DefinitionFinder}: go-to-definition for identifiers in JML text.
 *
 * <p>Test data: {@code OpenJMLTest/lsp/testdata/testGoToDefinition/}.
 * Two files are compiled together in the same IAPI context so that cross-file
 * symbol resolution works:
 * <ul>
 *   <li>{@code Helper.java} — declares Java fields, ghost fields, model fields,
 *       Java methods, and a model method.</li>
 *   <li>{@code Primary.java} — references all of the above in JML clauses
 *       ({@code //@ requires ...}) and also declares its own set of ghost,
 *       model, and Java members for same-file tests.</li>
 * </ul>
 *
 * <p>Each test finds the cursor offset on a specific JML line, calls
 * {@link DefinitionFinder#findDefinition}, and asserts that the returned
 * location points to the expected file and declaration line.
 */
public class DefinitionFinderTest {

    private Path testdir;
    private String primaryUri, helperUri;
    private String primarySrc, helperSrc;

    @Before
    public void setUp() throws Exception {
        String root = System.getProperty("lsp.testdata");
        assertNotNull("System property lsp.testdata must be set", root);
        testdir = Path.of(root, "testGoToDefinition");
        assertTrue("testGoToDefinition directory must exist", testdir.toFile().isDirectory());

        primarySrc = Files.readString(testdir.resolve("Primary.java"));
        helperSrc  = Files.readString(testdir.resolve("Helper.java"));
        primaryUri = testdir.resolve("Primary.java").toUri().toString();
        helperUri  = testdir.resolve("Helper.java").toUri().toString();

        // Compile Primary.java with Helper.java on the sourcepath so that both
        // are attributed in the same IAPI context and their symbols are shared.
        OpenJMLSettings settings = new OpenJMLSettings();
        settings.sourcePath = testdir.toString();
        CheckRunner.checkFile(testdir.resolve("Primary.java").toString(), primaryUri, settings);
    }

    // -----------------------------------------------------------------------
    // Same-file: Java field referenced in JML
    // -----------------------------------------------------------------------

    @Test
    public void testJavaFieldSameFile() {
        Location loc = defAt(primaryUri, primarySrc, "requires pJavaField", "pJavaField");
        assertNotNull("Expected definition for pJavaField", loc);
        assertEquals("pJavaField must be in Primary.java", primaryUri, loc.getUri());
        assertEquals("pJavaField declaration line",
                lineOf(primarySrc, "public int pJavaField"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Same-file: ghost field referenced in JML
    // -----------------------------------------------------------------------

    @Test
    public void testGhostFieldSameFile() {
        Location loc = defAt(primaryUri, primarySrc, "requires pGhostField", "pGhostField");
        assertNotNull("Expected definition for pGhostField", loc);
        assertEquals("pGhostField must be in Primary.java", primaryUri, loc.getUri());
        assertEquals("pGhostField declaration line",
                lineOf(primarySrc, "ghost public int pGhostField"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Same-file: model field referenced in JML
    // -----------------------------------------------------------------------

    @Test
    public void testModelFieldSameFile() {
        Location loc = defAt(primaryUri, primarySrc, "requires pModelField", "pModelField");
        assertNotNull("Expected definition for pModelField", loc);
        assertEquals("pModelField must be in Primary.java", primaryUri, loc.getUri());
        assertEquals("pModelField declaration line",
                lineOf(primarySrc, "model public int pModelField"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Same-file: Java method called in JML
    // -----------------------------------------------------------------------

    @Test
    public void testJavaMethodSameFile() {
        Location loc = defAt(primaryUri, primarySrc, "requires pJavaMethod", "pJavaMethod");
        assertNotNull("Expected definition for pJavaMethod", loc);
        assertEquals("pJavaMethod must be in Primary.java", primaryUri, loc.getUri());
        assertEquals("pJavaMethod declaration line",
                lineOf(primarySrc, "public int pJavaMethod"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Same-file: model method called in JML
    // -----------------------------------------------------------------------

    @Test
    public void testModelMethodSameFile() {
        Location loc = defAt(primaryUri, primarySrc, "requires pModelMethod", "pModelMethod");
        assertNotNull("Expected definition for pModelMethod", loc);
        assertEquals("pModelMethod must be in Primary.java", primaryUri, loc.getUri());
        assertEquals("pModelMethod declaration line",
                lineOf(primarySrc, "model public int pModelMethod"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Cross-file: Java field (JCFieldAccess — cursor on field name)
    // -----------------------------------------------------------------------

    @Test
    public void testJavaFieldCrossFile() {
        Location loc = defAt(primaryUri, primarySrc, "requires helper.hJavaField", "hJavaField");
        assertNotNull("Expected definition for hJavaField", loc);
        assertEquals("hJavaField must be in Helper.java", helperUri, loc.getUri());
        assertEquals("hJavaField declaration line",
                lineOf(helperSrc, "public int hJavaField"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Cross-file: ghost field (JCFieldAccess)
    // -----------------------------------------------------------------------

    @Test
    public void testGhostFieldCrossFile() {
        Location loc = defAt(primaryUri, primarySrc, "requires helper.hGhostField", "hGhostField");
        assertNotNull("Expected definition for hGhostField", loc);
        assertEquals("hGhostField must be in Helper.java", helperUri, loc.getUri());
        assertEquals("hGhostField declaration line",
                lineOf(helperSrc, "ghost public int hGhostField"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Cross-file: model field (JCFieldAccess)
    // -----------------------------------------------------------------------

    @Test
    public void testModelFieldCrossFile() {
        Location loc = defAt(primaryUri, primarySrc, "requires helper.hModelField", "hModelField");
        assertNotNull("Expected definition for hModelField", loc);
        assertEquals("hModelField must be in Helper.java", helperUri, loc.getUri());
        assertEquals("hModelField declaration line",
                lineOf(helperSrc, "model public int hModelField"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Cross-file: Java method (JCFieldAccess on method name in call)
    // -----------------------------------------------------------------------

    @Test
    public void testJavaMethodCrossFile() {
        Location loc = defAt(primaryUri, primarySrc, "requires helper.hJavaMethod", "hJavaMethod");
        assertNotNull("Expected definition for hJavaMethod", loc);
        assertEquals("hJavaMethod must be in Helper.java", helperUri, loc.getUri());
        assertEquals("hJavaMethod declaration line",
                lineOf(helperSrc, "public int hJavaMethod"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Cross-file: model method (JCFieldAccess on method name in call)
    // -----------------------------------------------------------------------

    @Test
    public void testModelMethodCrossFile() {
        Location loc = defAt(primaryUri, primarySrc, "requires helper.hModelMethod", "hModelMethod");
        assertNotNull("Expected definition for hModelMethod", loc);
        assertEquals("hModelMethod must be in Helper.java", helperUri, loc.getUri());
        assertEquals("hModelMethod declaration line",
                lineOf(helperSrc, "model public int hModelMethod"),
                loc.getRange().getStart().getLine());
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Return the 0-indexed line number of the first line in {@code source}
     * that contains {@code substr}.
     */
    private static int lineOf(String source, String substr) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(substr)) return i;
        }
        fail("Not found in source: «" + substr + "»");
        return -1;
    }

    /**
     * Find the definition of the identifier {@code id} at its first occurrence
     * on the source line that contains {@code contextString}.
     *
     * <p>{@code contextString} disambiguates when the same identifier appears
     * both at its declaration and in a JML clause — e.g.
     * {@code "requires pJavaField"} selects the usage line, not the field
     * declaration line.
     */
    private Location defAt(String uri, String source, String contextString, String id) {
        int lineStart = source.indexOf(contextString);
        assertTrue("Context string not found: «" + contextString + "»", lineStart >= 0);
        int idPos = source.indexOf(id, lineStart);
        assertTrue("Identifier «" + id + "» not found after context string", idPos >= 0);

        int[] lc = DefinitionFinder.offsetToLineCol(source, idPos);
        return DefinitionFinder.findDefinition(uri, lc[0], lc[1],
                Map.of(primaryUri, primarySrc, helperUri, helperSrc),
                CheckRunner.getASTCache());
    }
}
