package org.openjml.lsp.test;

import org.eclipse.lsp4j.DocumentSymbol;
import org.eclipse.lsp4j.SymbolKind;
import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.DocumentSymbolProvider;

import java.util.List;
import java.util.Optional;

import static org.junit.Assert.*;

/**
 * Tests for {@link DocumentSymbolProvider}: textDocument/documentSymbol (Outline panel).
 *
 * <p>The provider returns only JML-specific symbols (ghost, model) so the OpenJML
 * outline complements rather than duplicates the Java outline from the Red Hat extension.
 * A regular Java class appears as a container only when it has JML children.
 */
public class DocumentSymbolTest extends LspTestBase {

    private static final String URI = "file:///DocSymTest.java";

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Run --check to populate the ASTCache, then build document symbols. */
    private List<DocumentSymbol> symbolsFor(String source) {
        checkContent(URI, source);
        ASTCache.Entry entry = CheckRunner.getASTCache().get(URI);
        assertNotNull("ASTCache must have an entry after --check", entry);
        return DocumentSymbolProvider.fromAst(entry.ast(), source);
    }

    private static DocumentSymbol findSymbol(List<DocumentSymbol> symbols, String name) {
        for (DocumentSymbol s : symbols) {
            if (name.equals(s.getName())) return s;
            if (s.getChildren() != null) {
                DocumentSymbol child = findSymbol(s.getChildren(), name);
                if (child != null) return child;
            }
        }
        return null;
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /** A plain Java class with no JML members produces no symbols. */
    @Test
    public void testPlainClassProducesNoSymbols() {
        String source =
                "public class DocSymTest {\n" +
                "    public int value;\n" +
                "    public int getValue() { return value; }\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        assertTrue("Plain Java class with no JML members must produce no symbols", syms.isEmpty());
    }

    /** A class with a ghost field appears as a container with the ghost field as a child. */
    @Test
    public void testGhostFieldIncluded() {
        String source =
                "public class DocSymTest {\n" +
                "    //@ ghost int ghostField;\n" +
                "    public int realField;\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        assertEquals("Expected exactly one top-level symbol (class container)", 1, syms.size());
        DocumentSymbol cls = syms.get(0);
        List<DocumentSymbol> children = cls.getChildren();
        assertNotNull("Class must have children", children);

        // Ghost field must be a DIRECT CHILD of the class
        Optional<DocumentSymbol> ghost = children.stream()
                .filter(c -> "ghostField".equals(c.getName())).findFirst();
        assertTrue("Ghost field must be a direct child of the class", ghost.isPresent());
        assertEquals(SymbolKind.Field, ghost.get().getKind());
        assertEquals("(ghost)", ghost.get().getDetail());

        // Regular field must NOT appear (Red Hat Java outline covers it)
        Optional<DocumentSymbol> real = children.stream()
                .filter(c -> "realField".equals(c.getName())).findFirst();
        assertFalse("Regular field must not appear in JML-only outline", real.isPresent());
    }

    /** A class with a model method appears as a container with the method as a child. */
    @Test
    public void testModelMethodIncluded() {
        String source =
                "public class DocSymTest {\n" +
                "    //@ model int modelMethod() { return 0; }\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        assertEquals("Expected exactly one top-level symbol (class container)", 1, syms.size());
        DocumentSymbol cls = syms.get(0);
        List<DocumentSymbol> children = cls.getChildren();
        assertNotNull("Class must have children", children);

        Optional<DocumentSymbol> model = children.stream()
                .filter(c -> "modelMethod".equals(c.getName())).findFirst();
        assertTrue("Model method must be a direct child of the class", model.isPresent());
        assertEquals(SymbolKind.Method, model.get().getKind());
        assertEquals("(model)", model.get().getDetail());
    }

    /** Selection range must correctly identify the ghost field name position. */
    @Test
    public void testSelectionRangePointsToGhostName() {
        String source =
                "public class DocSymTest {\n" +    // line 0
                "    //@ ghost int ghostField;\n" + // line 1: "ghostField" starts at col 19
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        DocumentSymbol ghost = findSymbol(syms, "ghostField");
        assertNotNull("Ghost field must appear in symbols", ghost);
        assertEquals(1, ghost.getSelectionRange().getStart().getLine());
        assertEquals(18, ghost.getSelectionRange().getStart().getCharacter());
    }

    /** selectionRange must be contained within fullRange. */
    @Test
    public void testSelectionRangeContainedInFullRange() {
        String source =
                "public class DocSymTest {\n" +
                "    //@ ghost int ghostField;\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        DocumentSymbol ghost = findSymbol(syms, "ghostField");
        assertNotNull(ghost);
        // fullRange.start <= selectionRange.start
        assertTrue(ghost.getRange().getStart().getLine()
                <= ghost.getSelectionRange().getStart().getLine());
        // fullRange.end >= selectionRange.end
        int fullEndLine = ghost.getRange().getEnd().getLine();
        int selEndLine  = ghost.getSelectionRange().getEnd().getLine();
        assertTrue(fullEndLine > selEndLine
                || (fullEndLine == selEndLine
                    && ghost.getRange().getEnd().getCharacter()
                       >= ghost.getSelectionRange().getEnd().getCharacter()));
    }

    /** Both ghost and model members are shown; plain Java members are omitted. */
    @Test
    public void testMixedJmlAndJavaMembers() {
        String source =
                "public class DocSymTest {\n" +
                "    public int javaField;\n" +
                "    //@ ghost int ghostField;\n" +
                "    //@ model int modelField;\n" +
                "    public void javaMethod() {}\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        assertEquals(1, syms.size());
        List<DocumentSymbol> children = syms.get(0).getChildren();
        assertNotNull(children);

        assertTrue("ghostField must appear",
                children.stream().anyMatch(c -> "ghostField".equals(c.getName())));
        assertTrue("modelField must appear",
                children.stream().anyMatch(c -> "modelField".equals(c.getName())));
        assertFalse("javaField must NOT appear",
                children.stream().anyMatch(c -> "javaField".equals(c.getName())));
        assertFalse("javaMethod must NOT appear",
                children.stream().anyMatch(c -> "javaMethod".equals(c.getName())));
    }
}
