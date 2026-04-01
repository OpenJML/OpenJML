package org.openjml.lsp.test;

import org.eclipse.lsp4j.SemanticTokens;
import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.SemanticTokensProvider;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

/**
 * Tests for the AST-walker path in {@link SemanticTokensProvider}:
 * {@link SemanticTokensProvider#computeTokensFromAst}.
 *
 * <p>Unlike {@link SemanticTokensTest}, which tests the regex-fallback path via
 * {@code computeTokens(src)}, these tests populate the AST cache via
 * {@link LspTestBase#checkContent} and then call {@code computeTokensFromAst}
 * directly.  This exercises {@code SemanticTokensProvider.JmlAstWalker}, which
 * traverses the attributed JML AST to emit only genuine JML keyword tokens —
 * preventing false highlights for Java identifiers that share a name with JML
 * clause keywords.
 */
public class SemanticTokensAstTest extends LspTestBase {

    // -----------------------------------------------------------------------
    // Helpers (duplicated from SemanticTokensTest to keep the class standalone)
    // -----------------------------------------------------------------------

    record Token(int line, int col, int length, int type) {}

    /** Decode the flat delta-encoded LSP token data into absolute (line, col) tokens. */
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

    private static long countByType(List<Token> tokens, int type) {
        return tokens.stream().filter(t -> t.type() == type).count();
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    /**
     * A {@code requires} clause in the AST must produce a keyword token via the
     * AST walker.  The JML keyword must be highlighted at the correct line.
     */
    @Test
    public void testAstWalkerRequiresKeyword() throws Exception {
        String uri = "file:///SemTokAst1.java";
        String source =
                "public class SemTokAst1 {\n" +
                "    //@ requires x > 0;\n" +
                "    public int m(int x) { return x; }\n" +
                "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST cache must have entry after checkContent", entry);

        SemanticTokens st = SemanticTokensProvider.computeTokensFromAst(entry, source);
        List<Token> tokens = decode(st);

        assertFalse("Expected at least one token from AST walker for 'requires'", tokens.isEmpty());
        assertTrue("Expected a keyword token (requires)",
                tokens.stream().anyMatch(t -> t.type() == SemanticTokensProvider.TT_KEYWORD));
    }

    /**
     * An {@code ensures} clause with {@code \\result} in the AST must produce
     * a keyword token for {@code ensures} and a macro token for {@code \\result}.
     */
    @Test
    public void testAstWalkerEnsuresAndResult() throws Exception {
        String uri = "file:///SemTokAst2.java";
        String source =
                "public class SemTokAst2 {\n" +
                "    //@ ensures \\result >= 0;\n" +
                "    public int m() { return 1; }\n" +
                "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST cache must have entry after checkContent", entry);

        SemanticTokens st = SemanticTokensProvider.computeTokensFromAst(entry, source);
        List<Token> tokens = decode(st);

        assertTrue("Expected keyword token for 'ensures'",
                countByType(tokens, SemanticTokensProvider.TT_KEYWORD) >= 1);
        assertTrue("Expected macro token for '\\result'",
                countByType(tokens, SemanticTokensProvider.TT_MACRO) >= 1);
    }

    /**
     * A Java identifier that happens to share a name with a JML keyword ({@code requires}
     * used as a Java field name) must not be highlighted as a keyword by the AST walker.
     * The AST walker only emits tokens for genuine JML AST nodes; it does not
     * text-scan for keyword strings.
     */
    @Test
    public void testAstWalkerDoesNotHighlightJavaIdentifierNamedRequires() throws Exception {
        String uri = "file:///SemTokAst3.java";
        // 'requires' here is a plain Java field name, not a JML clause keyword.
        String source =
                "public class SemTokAst3 {\n" +
                "    String requires = \"test\";\n" +
                "    public String get() { return requires; }\n" +
                "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST cache must have entry after checkContent", entry);

        SemanticTokens st = SemanticTokensProvider.computeTokensFromAst(entry, source);
        List<Token> tokens = decode(st);

        boolean hasKeyword = tokens.stream()
                .anyMatch(t -> t.type() == SemanticTokensProvider.TT_KEYWORD);
        assertFalse("Java identifier 'requires' must not produce a keyword token", hasKeyword);
    }
}
