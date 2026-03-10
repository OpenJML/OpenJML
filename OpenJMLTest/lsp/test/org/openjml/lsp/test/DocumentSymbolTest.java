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
 * <p>Calls {@link CheckRunner#check} to attribute the AST (populates {@link ASTCache}),
 * then calls {@link DocumentSymbolProvider#fromAst} directly and asserts on the
 * hierarchical symbol tree.
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

    /** A simple class must appear as a top-level Class symbol. */
    @Test
    public void testClassSymbol() {
        String source =
                "public class DocSymTest {\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        assertEquals("Expected exactly one top-level symbol", 1, syms.size());
        DocumentSymbol cls = syms.get(0);
        assertEquals("DocSymTest", cls.getName());
        assertEquals(SymbolKind.Class, cls.getKind());
    }

    /** Methods and fields should appear as children of the enclosing class. */
    @Test
    public void testMethodAndFieldChildren() {
        String source =
                "public class DocSymTest {\n" +
                "    private int value;\n" +
                "    public int getValue() { return value; }\n" +
                "    public void setValue(int v) { this.value = v; }\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        assertEquals(1, syms.size());
        DocumentSymbol cls = syms.get(0);
        List<DocumentSymbol> children = cls.getChildren();
        assertNotNull("Class must have children", children);

        Optional<DocumentSymbol> field = children.stream()
                .filter(c -> "value".equals(c.getName())).findFirst();
        assertTrue("Field 'value' must appear", field.isPresent());
        assertEquals(SymbolKind.Field, field.get().getKind());

        Optional<DocumentSymbol> getter = children.stream()
                .filter(c -> "getValue".equals(c.getName())).findFirst();
        assertTrue("Method 'getValue' must appear", getter.isPresent());
        assertEquals(SymbolKind.Method, getter.get().getKind());

        Optional<DocumentSymbol> setter = children.stream()
                .filter(c -> "setValue".equals(c.getName())).findFirst();
        assertTrue("Method 'setValue' must appear", setter.isPresent());
        assertEquals(SymbolKind.Method, setter.get().getKind());
    }

    /** Constructors must appear as Constructor symbols using the class name. */
    @Test
    public void testConstructorSymbol() {
        String source =
                "public class DocSymTest {\n" +
                "    public DocSymTest() {}\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        DocumentSymbol cls = syms.get(0);
        List<DocumentSymbol> children = cls.getChildren();
        assertNotNull("Class must have children", children);
        Optional<DocumentSymbol> ctor = children.stream()
                .filter(c -> "DocSymTest".equals(c.getName())
                          && c.getKind() == SymbolKind.Constructor)
                .findFirst();
        assertTrue("Constructor must appear as Constructor kind with class name", ctor.isPresent());
    }

    /** An interface must appear with SymbolKind.Interface. */
    @Test
    public void testInterfaceSymbol() {
        String source =
                "public interface DocSymTest {\n" +
                "    int compute(int x);\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        assertEquals(1, syms.size());
        assertEquals(SymbolKind.Interface, syms.get(0).getKind());

        DocumentSymbol method = findSymbol(syms, "compute");
        assertNotNull("Abstract method 'compute' must appear", method);
        assertEquals(SymbolKind.Method, method.getKind());
    }

    /** An enum must appear with SymbolKind.Enum. */
    @Test
    public void testEnumSymbol() {
        String source =
                "public enum DocSymTest {\n" +
                "    A, B, C;\n" +
                "    public int ordinalPlusOne() { return ordinal() + 1; }\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        assertEquals(1, syms.size());
        assertEquals(SymbolKind.Enum, syms.get(0).getKind());

        DocumentSymbol method = findSymbol(syms, "ordinalPlusOne");
        assertNotNull("Method in enum must appear", method);
        assertEquals(SymbolKind.Method, method.getKind());
    }

    /** Selection range must correctly identify the symbol name position. */
    @Test
    public void testSelectionRangePointsToName() {
        String source =
                "public class DocSymTest {\n" +  // "DocSymTest" starts at col 13, line 0
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        assertEquals(1, syms.size());
        DocumentSymbol cls = syms.get(0);
        // selectionRange must start at the 'D' of "DocSymTest" (line 0, col 13)
        assertEquals(0, cls.getSelectionRange().getStart().getLine());
        assertEquals(13, cls.getSelectionRange().getStart().getCharacter());
    }

    /** JML ghost declarations should appear alongside regular Java declarations. */
    @Test
    public void testGhostFieldIncluded() {
        String source =
                "public class DocSymTest {\n" +
                "    //@ ghost int ghostField;\n" +
                "    public int realField;\n" +
                "}\n";
        List<DocumentSymbol> syms = symbolsFor(source);
        DocumentSymbol ghost = findSymbol(syms, "ghostField");
        assertNotNull("Ghost field must appear in document symbols", ghost);
        assertEquals(SymbolKind.Field, ghost.getKind());
        assertEquals("ghost", ghost.getDetail());
        DocumentSymbol real = findSymbol(syms, "realField");
        assertNotNull("Real field must appear in document symbols", real);
        assertNull("Regular field must have no detail", real.getDetail());
    }
}
