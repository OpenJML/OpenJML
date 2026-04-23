package org.openjml.lsp.test;

import org.eclipse.lsp4j.SemanticTokens;
import org.junit.Test;
import org.openjml.lsp.SemanticTokensProvider;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

/**
 * Tests for {@link SemanticTokensProvider}: JML semantic token generation.
 *
 * <p>Token data is a flat list of 5-integer tuples:
 * {@code [deltaLine, deltaStartChar, length, tokenTypeIndex, tokenModifiers]}.
 */
public class SemanticTokensTest {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    record Token(int line, int col, int length, int type) {}

    /** Decode the flat delta-encoded data into absolute (line, col) tokens. */
    private static List<Token> decode(SemanticTokens st) {
        List<Integer> data = st.getData();
        List<Token> result = new ArrayList<>();
        int line = 0, col = 0;
        for (int i = 0; i + 4 < data.size(); i += 5) {
            int dLine = data.get(i);
            int dCol  = data.get(i + 1);
            int len   = data.get(i + 2);
            int type  = data.get(i + 3);
            line += dLine;
            col   = (dLine == 0) ? col + dCol : dCol;
            result.add(new Token(line, col, len, type));
        }
        return result;
    }

    /** Find the first token with the given token type on any line. */
    private static Token findByType(List<Token> tokens, int type) {
        return tokens.stream().filter(t -> t.type() == type).findFirst().orElse(null);
    }

    /** Count tokens of the given type. */
    private static long countByType(List<Token> tokens, int type) {
        return tokens.stream().filter(t -> t.type() == type).count();
    }

    // -----------------------------------------------------------------------
    // Tests: single-line JML comments (//@)
    // -----------------------------------------------------------------------

    @Test
    public void testNoTokensOutsideJml() {
        String src =
                "public class Foo {\n"
                + "    public int x = 0;\n"
                + "    public void m() {}\n"
                + "}\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        assertTrue("No JML tokens expected in plain Java", tokens.isEmpty());
    }

    @Test
    public void testRequiresKeyword() {
        String src =
                "public class Foo {\n"
                + "    //@ requires x >= 0;\n"
                + "    public void m(int x) {}\n"
                + "}\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        assertEquals("Expected exactly one token", 1, tokens.size());
        Token t = tokens.get(0);
        assertEquals("keyword type", SemanticTokensProvider.TT_KEYWORD, t.type());
        assertEquals("on line 1", 1, t.line());
        assertEquals("length of 'requires'", "requires".length(), t.length());
    }

    @Test
    public void testEnsuresKeyword() {
        String src =
                "//@ ensures \\result >= 0;\n"
                + "public int m() { return 1; }\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        // Should see "ensures" (keyword) and "\result" (backslash token)
        long kw   = countByType(tokens, SemanticTokensProvider.TT_KEYWORD);
        long bs   = countByType(tokens, SemanticTokensProvider.BACKSLASH_TOKEN_TYPE);
        assertEquals("one keyword (ensures)", 1, kw);
        assertEquals("one backslash token (\\result)", 1, bs);
    }

    @Test
    public void testBackslashResult() {
        String src = "//@ ensures \\result >= 0;\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        Token bsTok = findByType(tokens, SemanticTokensProvider.BACKSLASH_TOKEN_TYPE);
        assertNotNull("\\result token must exist", bsTok);
        assertEquals("length includes backslash", "\\result".length(), bsTok.length());
    }

    @Test
    public void testBackslashOld() {
        String src = "//@ ensures x == \\old(x);\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        Token bsTok = findByType(tokens, SemanticTokensProvider.BACKSLASH_TOKEN_TYPE);
        assertNotNull("\\old token must exist", bsTok);
        assertEquals("\\old".length(), bsTok.length());
    }

    @Test
    public void testBackslashForall() {
        String src = "//@ invariant (\\forall int i; i >= 0; a[i] >= 0);\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        long bs = countByType(tokens, SemanticTokensProvider.BACKSLASH_TOKEN_TYPE);
        assertTrue("\\forall should produce a backslash token", bs >= 1);
    }

    @Test
    public void testPureModifier() {
        String src =
                "//@ pure\n"
                + "public int m() { return 0; }\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        assertEquals("pure produces one modifier token", 1, tokens.size());
        assertEquals(SemanticTokensProvider.TT_MODIFIER, tokens.get(0).type());
    }

    @Test
    public void testGhostAndModelModifiers() {
        String src =
                "//@ ghost public int g = 0;\n"
                + "//@ model public int m;\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        long kwCount = countByType(tokens, SemanticTokensProvider.TT_KEYWORD);
        assertTrue("'ghost' and 'model' both produce keyword tokens", kwCount >= 2);
    }

    @Test
    public void testInvariantKeyword() {
        String src = "//@ invariant x >= 0;\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        assertFalse("invariant should produce at least one token", tokens.isEmpty());
        assertEquals(SemanticTokensProvider.TT_KEYWORD, tokens.get(0).type());
        assertEquals("invariant".length(), tokens.get(0).length());
    }

    @Test
    public void testMultipleLinesMultipleTokens() {
        String src =
                "public class Foo {\n"
                + "    //@ requires x >= 0;\n"
                + "    //@ ensures \\result >= 0;\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        long kw = countByType(tokens, SemanticTokensProvider.TT_KEYWORD);
        long bs = countByType(tokens, SemanticTokensProvider.BACKSLASH_TOKEN_TYPE);
        assertEquals("requires + ensures = 2 keywords", 2, kw);
        assertEquals("\\result = 1 backslash token", 1, bs);
    }

    @Test
    public void testNonJmlLineProducesNoTokens() {
        // "requires" appearing in regular Java code must NOT be highlighted.
        String src =
                "public class Foo {\n"
                + "    String requires = \"test\";\n"  // not in JML context
                + "}\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        assertTrue("No tokens expected in plain Java source", tokens.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Tests: block JML comments (/*@ ... @*/)
    // -----------------------------------------------------------------------

    @Test
    public void testBlockJmlComment() {
        String src =
                "/*@ requires x >= 0;\n"
                + "  @ ensures \\result >= x;\n"
                + "  @*/\n"
                + "public int m(int x) { return x; }\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        long kw = countByType(tokens, SemanticTokensProvider.TT_KEYWORD);
        long bs = countByType(tokens, SemanticTokensProvider.BACKSLASH_TOKEN_TYPE);
        assertTrue("requires + ensures in block comment", kw >= 2);
        assertTrue("\\result in block comment", bs >= 1);
    }

    @Test
    public void testSingleLineBlockJmlComment() {
        String src = "/*@ invariant x >= 0; @*/\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        long kw = countByType(tokens, SemanticTokensProvider.TT_KEYWORD);
        assertEquals("invariant in single-line block comment", 1, kw);
    }

    // -----------------------------------------------------------------------
    // Tests: delta encoding
    // -----------------------------------------------------------------------

    @Test
    public void testDeltaEncodingCorrectness() {
        String src =
                "//@ requires x >= 0;\n"
                + "//@ ensures \\result >= 0;\n";
        SemanticTokens st   = SemanticTokensProvider.computeTokens(src);
        List<Integer>  data = st.getData();
        // 3 tokens (requires, ensures, \result) × 5 ints = 15 entries
        assertEquals(15, data.size());

        // First token (requires on line 0): deltaLine=0, deltaCol=col of 'requires'
        assertEquals("first token deltaLine", 0, (int) data.get(0));
        int requiresCol = "//@ ".length();
        assertEquals("first token deltaCol", requiresCol, (int) data.get(1));
        assertEquals("first token length", "requires".length(), (int) data.get(2));
        assertEquals("first token type", SemanticTokensProvider.TT_KEYWORD, (int) data.get(3));
        assertEquals("first token modifiers", 0, (int) data.get(4));

        // Second token (ensures on line 1): deltaLine=1
        assertEquals("second token deltaLine", 1, (int) data.get(5));
    }

    @Test
    public void testTokensOnSameLineDeltaEncoding() {
        // Two tokens on the same line
        String src = "//@ requires x >= 0 && \\old(x) >= 0;\n";
        List<Token> tokens = decode(SemanticTokensProvider.computeTokens(src));
        // requires (keyword) + \old (backslash token) — both on line 0
        assertEquals(2, tokens.size());
        assertEquals(0, tokens.get(0).line());
        assertEquals(0, tokens.get(1).line());
        assertTrue("\\old must be after requires", tokens.get(1).col() > tokens.get(0).col());
    }
}
