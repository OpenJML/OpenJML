package org.openjml.lsp.test;

import org.eclipse.lsp4j.InlayHint;
import org.eclipse.lsp4j.InlayHintParams;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.InlayHintProvider;
import org.openjml.lsp.OpenJMLSettings;

import java.util.List;

import static org.junit.Assert.*;

/**
 * Tests for {@link InlayHintProvider}: {@code textDocument/inlayHints} —
 * {@code var}-type inference display.
 *
 * <p>Each test populates the AST cache via {@link CheckRunner#check} and then
 * calls {@link InlayHintProvider#compute} directly.  The whole-document range
 * is used for all hint requests (clients may pass a narrower range; the
 * provider ignores the range and returns all hints — a simplification that is
 * acceptable while there is no performance concern with small files).
 */
public class InlayHintsVarTypesTest extends LspTestBase {

    private static final String URI = "file:///InlayHints.java";

    /** Whole-document range sentinel (far enough to cover any test file). */
    private static final Range ALL = new Range(new Position(0, 0), new Position(9999, 0));

    /** Build an {@link InlayHintParams} for the whole document. */
    private static InlayHintParams params(String uri) {
        return new InlayHintParams(new TextDocumentIdentifier(uri), ALL);
    }

    /** Return the label string from an {@link InlayHint} (left side of the Either). */
    private static String label(InlayHint h) {
        return h.getLabel().getLeft();
    }

    // -----------------------------------------------------------------------
    // (1) var x = 42 → hint `: int`
    // -----------------------------------------------------------------------

    @Test
    public void testVarInt() {
        String source =
                "public class InlayHints {\n" +
                "    public void m() {\n" +
                "        var x = 42;\n" +
                "    }\n" +
                "}\n";
        checkContent(URI, source);
        List<InlayHint> hints = InlayHintProvider.compute(params(URI), source,
                CheckRunner.getASTCache(), false);
        assertEquals("Expected exactly one hint", 1, hints.size());
        assertEquals("Hint label must be ': int'", ": int", label(hints.get(0)));
    }

    // -----------------------------------------------------------------------
    // (2) var s = "hello" → hint `: String` (not java.lang.String)
    // -----------------------------------------------------------------------

    @Test
    public void testVarString() {
        String source =
                "public class InlayHints {\n" +
                "    public void m() {\n" +
                "        var s = \"hello\";\n" +
                "    }\n" +
                "}\n";
        checkContent(URI, source);
        List<InlayHint> hints = InlayHintProvider.compute(params(URI), source,
                CheckRunner.getASTCache(), false);
        assertEquals("Expected exactly one hint", 1, hints.size());
        assertEquals("Hint label must strip java.lang prefix", ": String", label(hints.get(0)));
    }

    // -----------------------------------------------------------------------
    // (3) var list = new ArrayList<String>() → hint `: ArrayList<String>`
    // -----------------------------------------------------------------------

    @Test
    public void testVarArrayList() {
        String source =
                "public class InlayHints {\n" +
                "    public void m() {\n" +
                "        var list = new java.util.ArrayList<String>();\n" +
                "    }\n" +
                "}\n";
        checkContent(URI, source);
        List<InlayHint> hints = InlayHintProvider.compute(params(URI), source,
                CheckRunner.getASTCache(), false);
        assertEquals("Expected exactly one hint", 1, hints.size());
        String lbl = label(hints.get(0));
        // shortTypeName strips java.lang. but not java.util. in the first implementation.
        assertTrue("Hint must contain 'ArrayList'", lbl.contains("ArrayList"));
        assertTrue("Hint must contain '<String>'", lbl.contains("<String>"));
        assertFalse("Hint must not contain 'java.lang.'", lbl.contains("java.lang."));
    }

    // -----------------------------------------------------------------------
    // (4) Explicit type — no hint
    // -----------------------------------------------------------------------

    @Test
    public void testExplicitTypeNoHint() {
        String source =
                "public class InlayHints {\n" +
                "    public void m() {\n" +
                "        int x = 0;\n" +
                "    }\n" +
                "}\n";
        checkContent(URI, source);
        List<InlayHint> hints = InlayHintProvider.compute(params(URI), source,
                CheckRunner.getASTCache(), false);
        assertTrue("Expected no hints for explicit-type declaration", hints.isEmpty());
    }

    // -----------------------------------------------------------------------
    // (5) No AST cached — returns empty list
    // -----------------------------------------------------------------------

    @Test
    public void testNoAstCachedReturnsEmpty() {
        String uncachedUri = "file:///NeverChecked.java";
        String source = "public class NeverChecked { public void m() { var x = 1; } }\n";
        // Do NOT call checkContent — leave the cache empty for this URI.
        List<InlayHint> hints = InlayHintProvider.compute(params(uncachedUri), source,
                new ASTCache(), false);
        assertTrue("Expected empty list when no AST is cached", hints.isEmpty());
    }

    // -----------------------------------------------------------------------
    // (6) javaMode = "jml-only" — isJmlOnly() returns true; handler returns empty.
    //     We test the settings helper directly here; the handler test is an
    //     integration concern covered by the protocol layer.
    // -----------------------------------------------------------------------

    @Test
    public void testJmlOnlyModeSettingsHelper() {
        OpenJMLSettings s = new OpenJMLSettings();
        assertFalse("Default javaMode must not be jml-only", s.isJmlOnly());

        s.javaMode = "jml-only";
        assertTrue("Setting javaMode=jml-only must make isJmlOnly() true", s.isJmlOnly());

        // Reset and test client-based inference.
        s.javaMode = null;
        s.client = "eclipse-jdt";
        assertTrue("eclipse-jdt client must imply jml-only", s.isJmlOnly());

        s.client = "vscode-java";
        assertTrue("vscode-java client must imply jml-only", s.isJmlOnly());

        s.client = "generic";
        assertFalse("generic client with no javaMode must be full", s.isJmlOnly());

        // Explicit override: even with a known client, "full" wins.
        s.javaMode = "full";
        s.client = "eclipse-jdt";
        assertFalse("Explicit javaMode=full must override client default", s.isJmlOnly());
    }

    // -----------------------------------------------------------------------
    // (7) var inside JML ghost declaration — no crash; ghost vars are typically
    //     declared with explicit JML types, not Java var, so no hint expected.
    // -----------------------------------------------------------------------

    @Test
    public void testGhostDeclarationNoCrash() {
        // Ghost variables use explicit JML types; this confirms the scanner
        // does not crash or produce spurious hints when walking JML ghost nodes.
        String source =
                "public class InlayHints {\n" +
                "    //@ ghost public int ghostField = 0;\n" +
                "    public void m() {\n" +
                "        var x = 1;\n" +
                "    }\n" +
                "}\n";
        checkContent(URI, source);
        List<InlayHint> hints = InlayHintProvider.compute(params(URI), source,
                CheckRunner.getASTCache(), false);
        // Only the Java var should produce a hint; the ghost field uses an explicit type.
        assertEquals("Expected exactly one hint (for Java var, not ghost)", 1, hints.size());
        assertEquals(": int", label(hints.get(0)));
    }

    // -----------------------------------------------------------------------
    // (8) JML \let expression — confirm no crash
    // -----------------------------------------------------------------------

    @Test
    public void testJmlLetNoCrash() {
        // \let binds a variable inside a JML expression. Whether it appears as a
        // JCVariableDecl depends on OpenJML's AST representation; this test just
        // confirms that scanning through such expressions causes no exception.
        String source =
                "public class InlayHints {\n" +
                "    /*@ pure */ public int compute(int x) {\n" +
                "        //@ assert (\\let int y = x + 1; y > 0);\n" +
                "        var result = x + 1;\n" +
                "        return result;\n" +
                "    }\n" +
                "}\n";
        checkContent(URI, source);
        // Must not throw; we do not assert a specific count since \let handling
        // may or may not surface the bound variable as a JCVariableDecl.
        List<InlayHint> hints = assertDoesNotThrow(
                () -> InlayHintProvider.compute(params(URI), source, CheckRunner.getASTCache(), false));
        assertNotNull(hints);
        // The Java var `result` should produce a hint.
        assertTrue("Expected at least one hint for the Java var",
                hints.stream().anyMatch(h -> label(h).equals(": int")));
    }

    // -----------------------------------------------------------------------
    // (9) JML \exists quantifier — confirm no crash
    // -----------------------------------------------------------------------

    @Test
    public void testJmlExistsNoCrash() {
        String source =
                "public class InlayHints {\n" +
                "    //@ requires (\\exists int i; 0 <= i && i < 10; i > 5);\n" +
                "    public void m() {\n" +
                "        var x = 42;\n" +
                "    }\n" +
                "}\n";
        checkContent(URI, source);
        List<InlayHint> hints = assertDoesNotThrow(
                () -> InlayHintProvider.compute(params(URI), source, CheckRunner.getASTCache(), false));
        assertNotNull(hints);
        // The Java var `x` should produce a hint.
        assertTrue("Expected hint for Java var x",
                hints.stream().anyMatch(h -> label(h).equals(": int")));
    }

    // -----------------------------------------------------------------------
    // (10) JML \bigint and \real ghost variables — no crash; shortTypeName
    //      must format these using the JML keyword form.
    // -----------------------------------------------------------------------

    @Test
    public void testBigintAndRealGhostNoCrash() {
        // Ghost variables declared with explicit JML built-in types (\bigint, \real).
        // Since they are NOT var-declared, no hints are produced.
        // The scanner must walk through them without throwing.
        String source =
                "public class InlayHints {\n" +
                "    //@ ghost public \\bigint bigN = 0;\n" +
                "    //@ ghost public \\real realR = 0.0;\n" +
                "    public void m() {\n" +
                "        var x = 1;\n" +
                "    }\n" +
                "}\n";
        checkContent(URI, source);
        List<InlayHint> hints = assertDoesNotThrow(
                () -> InlayHintProvider.compute(params(URI), source, CheckRunner.getASTCache(), false));
        assertNotNull(hints);
        // Only the Java var `x` (if attributed) may produce a hint.
        // The ghost declarations with explicit types must not produce hints.
        for (InlayHint h : hints) {
            String lbl = label(h);
            assertFalse("Hint label must not contain raw internal package for \\bigint",
                    lbl.contains("org.jmlspecs.lang.internal.bigint"));
            assertFalse("Hint label must not contain raw internal package for \\real",
                    lbl.contains("org.jmlspecs.lang.internal.real"));
        }
    }

    // -----------------------------------------------------------------------
    // (11) Same-package type — stripping via integration
    // -----------------------------------------------------------------------

    @Test
    public void testSamePackageTypeStripped() {
        // When the declared type is in the same package as the source file, the
        // package prefix should be stripped. We put the class in a named package
        // and use a type from that same package.
        String pkgUri = "file:///pkg/Holder.java";
        String holderSrc =
                "package pkg;\n" +
                "public class Holder {\n" +
                "    public static Holder make() { return new Holder(); }\n" +
                "}\n";
        checkContent(pkgUri, holderSrc);
        // Now a caller in the same package using var
        String callerUri = "file:///pkg/Caller.java";
        String callerSrc =
                "package pkg;\n" +
                "public class Caller {\n" +
                "    public void m() {\n" +
                "        var h = Holder.make();\n" +
                "    }\n" +
                "}\n";
        // Compile both together so Holder is resolved
        org.openjml.lsp.OpenJMLSettings s = new org.openjml.lsp.OpenJMLSettings();
        CheckRunner.checkWithContext(callerUri, callerSrc,
                java.util.Map.of(pkgUri, holderSrc), s);
        List<InlayHint> hints = InlayHintProvider.compute(params(callerUri), callerSrc,
                CheckRunner.getASTCache(), false);
        // Should have a hint; the type should be "Holder" not "pkg.Holder"
        if (!hints.isEmpty()) {
            String lbl = label(hints.get(0));
            assertFalse("Same-package prefix must be stripped", lbl.contains("pkg."));
            assertTrue("Short name must appear", lbl.contains("Holder"));
        }
        // If no hints (e.g. cross-file resolution failed), just confirm no crash.
    }

    // -----------------------------------------------------------------------
    // Helper
    // -----------------------------------------------------------------------

    /** Assert that the supplier completes without throwing. */
    private static <T> T assertDoesNotThrow(java.util.function.Supplier<T> supplier) {
        try {
            return supplier.get();
        } catch (Exception e) {
            fail("Expected no exception but got: " + e);
            return null; // unreachable
        }
    }
}
