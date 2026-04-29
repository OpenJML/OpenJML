package org.openjml.lsp.test;

import org.eclipse.lsp4j.Location;
import org.junit.Before;
import org.junit.Test;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.DefinitionFinder;
import org.openjml.lsp.OpenJMLSettings;
import org.openjml.lsp.ReferenceFinder;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * Tests for {@link ReferenceFinder}: find-all-references for identifiers in JML text.
 *
 * <p>Reuses the same test-data directory as {@link DefinitionFinderTest}
 * ({@code OpenJMLTest/lsp/testdata/testGoToDefinition/}).
 */
public class ReferenceFinderTest {

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

        OpenJMLSettings settings = new OpenJMLSettings();
        settings.sourcePath = testdir.toString();
        CheckRunner.checkFile(testdir.resolve("Primary.java").toString(), primaryUri, settings);
    }

    // -----------------------------------------------------------------------
    // Java field: pJavaField
    // -----------------------------------------------------------------------

    @Test
    public void testJavaFieldRefs() {
        // Find uses of pJavaField in Primary.java (exclude declaration).
        List<Location> refs = refsAt(primaryUri, primarySrc,
                "requires pJavaField", "pJavaField", false);
        // Expected uses: requires pJavaField (line 9), i < pJavaField (forall), letVar = pJavaField (let)
        assertFalse("Expected at least one reference to pJavaField", refs.isEmpty());
        assertAllInFile(refs, primaryUri);
        assertContainsLine(refs, lineOf(primarySrc, "requires pJavaField >= 0"));
    }

    @Test
    public void testJavaFieldRefsIncludeDecl() {
        List<Location> refs = refsAt(primaryUri, primarySrc,
                "requires pJavaField", "pJavaField", true);
        // Must include the declaration line too
        assertContainsLine(refs, lineOf(primarySrc, "public int pJavaField"));
        assertContainsLine(refs, lineOf(primarySrc, "requires pJavaField >= 0"));
    }

    // -----------------------------------------------------------------------
    // Ghost field: pGhostField
    // -----------------------------------------------------------------------

    @Test
    public void testGhostFieldRefs() {
        List<Location> refs = refsAt(primaryUri, primarySrc,
                "requires pGhostField", "pGhostField", false);
        assertFalse("Expected reference to pGhostField in requires clause", refs.isEmpty());
        assertContainsLine(refs, lineOf(primarySrc, "requires pGhostField >= 0"));
    }

    // -----------------------------------------------------------------------
    // Cross-file: hJavaField declared in Helper, used in Primary
    // -----------------------------------------------------------------------

    @Test
    public void testCrossFileRefs() {
        // Cursor on the declaration of hJavaField in Helper.java.
        // References should include uses in Primary.java.
        List<Location> refs = refsAt(helperUri, helperSrc,
                "public int hJavaField", "hJavaField", false);
        // Primary.java has: requires helper.hJavaField >= 0
        boolean foundInPrimary = refs.stream()
                .anyMatch(loc -> primaryUri.equals(loc.getUri())
                        && loc.getRange().getStart().getLine()
                                == lineOf(primarySrc, "requires helper.hJavaField"));
        assertTrue("hJavaField use in Primary.java must be found", foundInPrimary);
    }

    // -----------------------------------------------------------------------
    // \forall bound variable: i declared and used in quantifier
    // -----------------------------------------------------------------------

    @Test
    public void testForallBoundVarRefs() {
        // Cursor on the first "i" in "i >= 0; i < pJavaField" — a JCIdent use site.
        // Using a use site avoids the ambiguity of `i` being a substring of `int`.
        List<Location> refs = refsAt(primaryUri, primarySrc,
                "i >= 0; i < pJavaField", "i", false);
        // i is used in: range "i >= 0" and value "i < pJavaField"
        assertTrue("Expected at least 2 uses of forall bound var i, got " + refs.size(),
                refs.size() >= 2);
        assertAllInFile(refs, primaryUri);
    }

    @Test
    public void testForallBoundVarRefsIncludeDecl() {
        // Same cursor (use site), but with includeDeclaration=true.
        List<Location> refs = refsAt(primaryUri, primarySrc,
                "i >= 0; i < pJavaField", "i", true);
        // Declaration + range use + value use = at least 3
        assertTrue("Expected at least 3 occurrences of forall bound var i (decl + uses), got " + refs.size(),
                refs.size() >= 3);
    }

    // -----------------------------------------------------------------------
    // \exists two bound variables: qi and qj
    // -----------------------------------------------------------------------

    @Test
    public void testExistsBoundVarsDistinct() {
        // qi should NOT be in qj's reference list and vice versa
        List<Location> qi = refsAt(primaryUri, primarySrc, "\\exists int qi, qj", "qi", false);
        List<Location> qj = refsAt(primaryUri, primarySrc, "\\exists int qi, qj", "qj", false);

        assertFalse("qi should have references", qi.isEmpty());
        assertFalse("qj should have references", qj.isEmpty());

        // qi references must not overlap qj references (different column positions)
        for (Location a : qi) {
            for (Location b : qj) {
                assertFalse("qi and qj references must not coincide",
                        a.getUri().equals(b.getUri())
                        && a.getRange().getStart().equals(b.getRange().getStart()));
            }
        }
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Find all references to the identifier {@code id} at its first occurrence on
     * the source line containing {@code contextString}.
     */
    private List<Location> refsAt(String uri, String source,
                                   String contextString, String id,
                                   boolean includeDeclaration) {
        int lineStart = source.indexOf(contextString);
        assertTrue("Context string not found: «" + contextString + "»", lineStart >= 0);
        int idPos = source.indexOf(id, lineStart);
        assertTrue("Identifier «" + id + "» not found after context string", idPos >= 0);

        int[] lc = DefinitionFinder.offsetToLineCol(source, idPos);
        return ReferenceFinder.findReferences(uri, lc[0], lc[1],
                Map.of(primaryUri, primarySrc, helperUri, helperSrc),
                CheckRunner.getASTCache(),
                includeDeclaration);
    }

    private static int lineOf(String source, String substr) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(substr)) return i;
        }
        fail("Not found in source: «" + substr + "»");
        return -1;
    }

    private static void assertAllInFile(List<Location> refs, String expectedUri) {
        for (Location loc : refs) {
            assertEquals("All refs should be in " + expectedUri, expectedUri, loc.getUri());
        }
    }

    private static void assertContainsLine(List<Location> refs, int expectedLine) {
        boolean found = refs.stream()
                .anyMatch(loc -> loc.getRange().getStart().getLine() == expectedLine);
        if (!found) {
            String lines = refs.stream()
                    .map(loc -> String.valueOf(loc.getRange().getStart().getLine()))
                    .collect(Collectors.joining(", "));
            fail("Expected a reference on line " + expectedLine + ", got lines: [" + lines + "]");
        }
    }
}
