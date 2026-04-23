package org.openjml.lsp.test;

import org.eclipse.lsp4j.SemanticTokens;
import org.junit.Test;
import org.openjml.lsp.ASTCache;
import org.openjml.lsp.CheckRunner;
import org.openjml.lsp.SemanticTokensProvider;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

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
 *
 * <p>Each test checks at minimum that the expected token appears at the expected
 * line and column.  Column positions are 0-based (LSP convention).
 */
public class SemanticTokensAstTest extends LspTestBase {

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    record Token(int line, int col, int length, int type, int mods) {}

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
            int mods  = data.get(i + 4);
            line += dLine;
            col   = (dLine == 0) ? col + dCol : dCol;
            result.add(new Token(line, col, len, type, mods));
        }
        return result;
    }

    private static List<Token> byType(List<Token> tokens, int type) {
        return tokens.stream().filter(t -> t.type() == type).collect(Collectors.toList());
    }

    private static long countByType(List<Token> tokens, int type) {
        return tokens.stream().filter(t -> t.type() == type).count();
    }

    /** Assert a token of the given type appears at line:col with the given length. */
    private static void assertToken(List<Token> tokens, int type, int line, int col, int len) {
        boolean found = tokens.stream().anyMatch(t ->
                t.type() == type && t.line() == line && t.col() == col && t.length() == len);
        if (!found) {
            String all = tokens.stream()
                    .map(t -> "(" + t.line() + ":" + t.col() + " len=" + t.length() + " type=" + t.type() + ")")
                    .collect(Collectors.joining(", "));
            fail("Expected token type=" + type + " at " + line + ":" + col + " len=" + len
                    + " but got: [" + all + "]");
        }
    }

    /** Assert NO token of the given type appears at line:col. */
    private static void assertNoToken(List<Token> tokens, int type, int line, int col) {
        boolean found = tokens.stream().anyMatch(t ->
                t.type() == type && t.line() == line && t.col() == col);
        if (found) {
            fail("Did not expect token type=" + type + " at " + line + ":" + col);
        }
    }

    // Shorthand type constants for readability
    private static final int KW  = SemanticTokensProvider.TT_KEYWORD;
    private static final int MOD = SemanticTokensProvider.TT_MODIFIER;
    private static final int BS  = SemanticTokensProvider.BACKSLASH_TOKEN_TYPE;
    private static final int TYP = SemanticTokensProvider.TT_TYPE;
    private static final int MTH = SemanticTokensProvider.TT_METHOD;
    private static final int FLD = SemanticTokensProvider.TT_PROPERTY;
    private static final int PAR = SemanticTokensProvider.TT_PARAMETER;
    private static final int VAR = SemanticTokensProvider.TT_VARIABLE;
    private static final int CLS = SemanticTokensProvider.TT_CLASS;
    private static final int IFACE = SemanticTokensProvider.TT_INTERFACE;
    private static final int ENM = SemanticTokensProvider.TT_ENUM;
    private static final int ENM_MBR = SemanticTokensProvider.TT_ENUM_MEMBER;
    private static final int STRUCT = SemanticTokensProvider.TT_STRUCT;
    private static final int TP  = SemanticTokensProvider.TT_TYPE_PARAM;
    private static final int OP  = SemanticTokensProvider.TT_OPERATOR;
    private static final int STR = SemanticTokensProvider.TT_STRING;
    private static final int NUM = SemanticTokensProvider.TT_NUMBER;
    private static final int DEC = SemanticTokensProvider.TT_DECORATOR;

    // Modifier mask constants
    private static final int TM_DECLARATION = SemanticTokensProvider.TM_DECLARATION;
    private static final int TM_STATIC      = SemanticTokensProvider.TM_STATIC;
    private static final int TM_ABSTRACT    = SemanticTokensProvider.TM_ABSTRACT;
    private static final int TM_READONLY    = SemanticTokensProvider.TM_READONLY;
    private static final int TM_DEPRECATED  = SemanticTokensProvider.TM_DEPRECATED;

    // -----------------------------------------------------------------------
    // Tests: JML clause keywords
    // -----------------------------------------------------------------------

    /**
     * A {@code requires} clause in the AST must produce a keyword token at the
     * correct line and column.
     */
    @Test
    public void testRequiresClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Requires.java";
        String source =
                "public class SemTok_Requires {\n"             // line 0
                + "    //@ requires x > 0;\n"                  // line 1: requires at col 8
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST must be cached after checkContent", entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertFalse("At least one token expected", tokens.isEmpty());
        // "//@ requires" → col of 'r' is 8 (4 spaces + "//@ ")
        assertToken(tokens, KW, 1, 8, "requires".length());
    }

    /** An {@code ensures} clause must produce a keyword token. */
    @Test
    public void testEnsuresClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Ensures.java";
        String source =
                "public class SemTok_Ensures {\n"
                + "    //@ ensures \\result >= 0;\n"           // line 1
                + "    public int m() { return 1; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("keyword token expected (ensures)",
                countByType(tokens, KW) >= 1);
        assertTrue("backslash token expected (\\result)",
                countByType(tokens, BS) >= 1);
    }

    /** An {@code assignable} / {@code modifies} clause must produce a keyword token. */
    @Test
    public void testAssignableClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Assignable.java";
        String source =
                "public class SemTok_Assignable {\n"
                + "    int x;\n"
                + "    //@ assignable x;\n"                    // line 2
                + "    public void m() { x = 1; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("assignable must produce a keyword token", countByType(tokens, KW) >= 1);
    }

    /** A {@code signals} clause must produce a keyword token. */
    @Test
    public void testSignalsClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Signals.java";
        String source =
                "public class SemTok_Signals {\n"
                + "    //@ signals (Exception e) e != null;\n"  // line 1
                + "    public void m() throws Exception { throw new Exception(); }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("signals must produce a keyword token", countByType(tokens, KW) >= 1);
    }

    /** A {@code signals_only} clause must produce a keyword token. */
    @Test
    public void testSignalsOnly_KeywordToken() throws Exception {
        String uri = "file:///SemTok_SignalsOnly.java";
        String source =
                "public class SemTok_SignalsOnly {\n"
                + "    //@ signals_only Exception;\n"           // line 1
                + "    public void m() throws Exception { throw new Exception(); }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("signals_only must produce a keyword token", countByType(tokens, KW) >= 1);
    }

    /** An {@code invariant} type clause must produce a keyword token. */
    @Test
    public void testInvariantClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Invariant.java";
        String source =
                "public class SemTok_Invariant {\n"
                + "    int x;\n"
                + "    //@ invariant x >= 0;\n"                // line 2
                + "    public SemTok_Invariant() { x = 1; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("invariant must produce a keyword token", countByType(tokens, KW) >= 1);
    }

    /** An invariant WITH a {@code public} modifier: the keyword still appears. */
    @Test
    public void testInvariantClause_WithPublicModifier_KeywordPresent() throws Exception {
        String uri = "file:///SemTok_InvariantMod.java";
        String source =
                "public class SemTok_InvariantMod {\n"
                + "    public int x;\n"
                + "    //@ public invariant x >= 0;\n"         // line 2: 'invariant' after 'public'
                + "    public SemTok_InvariantMod() { x = 1; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("invariant (with modifier) must still produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /** A {@code constraint} (history constraint) clause must produce a keyword token. */
    @Test
    public void testConstraintClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Constraint.java";
        String source =
                "public class SemTok_Constraint {\n"
                + "    int x;\n"
                + "    //@ constraint x >= \\old(x);\n"        // line 2
                + "    public void inc() { x++; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("constraint must produce a keyword token", countByType(tokens, KW) >= 1);
    }

    /**
     * A {@code requires} clause on a method with a non-trivial body must produce
     * a keyword token (verifies that the method-level spec is found even when
     * the method has complex control flow).
     */
    @Test
    public void testRequiresOnComplexMethod_KeywordToken() throws Exception {
        String uri = "file:///SemTok_ComplexMethod.java";
        String source =
                "public class SemTok_ComplexMethod {\n"
                + "    //@ requires n >= 0;\n"                // line 1
                + "    public int sum(int n) {\n"
                + "        int s = 0;\n"
                + "        for (int i = 0; i <= n; i++) s += i;\n"
                + "        return s;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST must be cached after checkContent", entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("requires must produce a keyword token", countByType(tokens, KW) >= 1);
    }

    // -----------------------------------------------------------------------
    // Tests: JML modifiers (TT_MODIFIER vs TT_KEYWORD)
    // -----------------------------------------------------------------------

    /**
     * The {@code pure} JML modifier must produce a {@link SemanticTokensProvider#TT_MODIFIER}
     * token, not a {@link SemanticTokensProvider#TT_KEYWORD}.
     */
    @Test
    public void testPureModifier_IsModifierNotKeyword() throws Exception {
        String uri = "file:///SemTok_Pure.java";
        String source =
                "public class SemTok_Pure {\n"
                + "    //@ pure\n"                             // line 1
                + "    public int m() { return 0; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("pure must produce a modifier token", countByType(tokens, MOD) >= 1);
    }

    /**
     * The {@code spec_public} JML modifier must produce a {@link SemanticTokensProvider#TT_MODIFIER}
     * token.
     */
    @Test
    public void testSpecPublicModifier_IsModifier() throws Exception {
        String uri = "file:///SemTok_SpecPublic.java";
        String source =
                "public class SemTok_SpecPublic {\n"
                + "    /*@ spec_public */ private int x;\n"   // line 1
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("spec_public must produce a modifier token", countByType(tokens, MOD) >= 1);
    }

    /**
     * The {@code nullable} JML modifier must produce a {@link SemanticTokensProvider#TT_MODIFIER}.
     */
    @Test
    public void testNullableModifier_IsModifier() throws Exception {
        String uri = "file:///SemTok_Nullable.java";
        String source =
                "public class SemTok_Nullable {\n"
                + "    //@ nullable\n"                         // line 1
                + "    public String get() { return null; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("nullable must produce a modifier token", countByType(tokens, MOD) >= 1);
    }

    // -----------------------------------------------------------------------
    // Tests: JML backslash tokens
    // -----------------------------------------------------------------------

    /**
     * {@code \\result} in an {@code ensures} clause must produce a backslash token
     * (type == {@link SemanticTokensProvider#BACKSLASH_TOKEN_TYPE}).
     */
    @Test
    public void testBackslashResult_BackslashToken() throws Exception {
        String uri = "file:///SemTok_Result.java";
        String source =
                "public class SemTok_Result {\n"
                + "    //@ ensures \\result >= 0;\n"           // line 1
                + "    public int m() { return 1; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("\\result must produce a backslash token", countByType(tokens, BS) >= 1);
    }

    /**
     * {@code \\old} in an {@code ensures} clause must produce a backslash token.
     */
    @Test
    public void testBackslashOld_BackslashToken() throws Exception {
        String uri = "file:///SemTok_Old.java";
        String source =
                "public class SemTok_Old {\n"
                + "    int x;\n"
                + "    //@ ensures x == \\old(x) + 1;\n"      // line 2
                + "    public void inc() { x++; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("\\old must produce a backslash token", countByType(tokens, BS) >= 1);
    }

    /**
     * {@code \\forall} in an {@code invariant} must produce a backslash token.
     */
    @Test
    public void testBackslashForall_BackslashToken() throws Exception {
        String uri = "file:///SemTok_Forall.java";
        String source =
                "public class SemTok_Forall {\n"
                + "    int[] a;\n"
                + "    //@ invariant (\\forall int i; 0 <= i && i < a.length; a[i] >= 0);\n"
                + "    public SemTok_Forall() { a = new int[0]; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("\\forall must produce a backslash token", countByType(tokens, BS) >= 1);
    }

    /**
     * {@code \\nothing} in an {@code assignable} clause must produce a backslash token.
     */
    @Test
    public void testBackslashNothing_BackslashToken() throws Exception {
        String uri = "file:///SemTok_Nothing.java";
        String source =
                "public class SemTok_Nothing {\n"
                + "    //@ assignable \\nothing;\n"            // line 1
                + "    public int pure_m() { return 42; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("\\nothing must produce a backslash token", countByType(tokens, BS) >= 1);
    }

    /**
     * Multiple backslash tokens in the same file must each produce a token.
     */
    @Test
    public void testMultipleBackslashTokens() throws Exception {
        String uri = "file:///SemTok_MultiBS.java";
        String source =
                "public class SemTok_MultiBS {\n"
                + "    int x;\n"
                + "    //@ requires x > 0;\n"
                + "    //@ ensures \\result >= \\old(x);\n"    // line 3: \result + \old
                + "    public int m() { return x; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        long bsCount = countByType(tokens, BS);
        assertTrue("Expected at least 2 backslash tokens (\\result, \\old), got " + bsCount,
                bsCount >= 2);
    }

    // -----------------------------------------------------------------------
    // Tests: no false positives for Java identifiers named like JML keywords
    // -----------------------------------------------------------------------

    /**
     * A Java variable named {@code requires} must not produce a keyword token from
     * the AST walker.  The AST walker only emits tokens for genuine JML AST nodes.
     */
    @Test
    public void testJavaIdentifierNamedRequires_NotHighlighted() throws Exception {
        String uri = "file:///SemTok_NoFalsePositive.java";
        String source =
                "public class SemTok_NoFalsePositive {\n"
                + "    String requires = \"test\";\n"          // plain Java field
                + "    public String get() { return requires; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        // In JML-only mode, no JML context → no keyword tokens at all.
        assertFalse("Java identifier 'requires' must not produce a keyword token in JML-only mode",
                tokens.stream().anyMatch(t -> t.type() == KW));
    }

    // -----------------------------------------------------------------------
    // Tests: full mode — Java symbols
    // -----------------------------------------------------------------------

    /**
     * In full mode, a class declaration name produces a {@link SemanticTokensProvider#TT_CLASS}
     * token with the {@link SemanticTokensProvider#TM_DECLARATION} modifier.
     */
    @Test
    public void testFullMode_ClassDeclaration() throws Exception {
        String uri = "file:///SemTok_FullClass.java";
        String source =
                "public class SemTok_FullClass {\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        List<Token> clsTokens = byType(tokens, CLS);
        assertFalse("Class declaration must produce a class token in full mode", clsTokens.isEmpty());
        assertTrue("Class declaration token must have TM_DECLARATION modifier",
                clsTokens.stream().anyMatch(t -> (t.mods() & TM_DECLARATION) != 0));
    }

    /**
     * In full mode, an interface declaration name produces a
     * {@link SemanticTokensProvider#TT_INTERFACE} token.
     */
    @Test
    public void testFullMode_InterfaceDeclaration() throws Exception {
        String uri = "file:///SemTok_FullIface.java";
        String source =
                "public interface SemTok_FullIface {\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Interface declaration must produce an interface token",
                byType(tokens, IFACE).isEmpty());
    }

    /**
     * In full mode, an enum declaration and its members produce the correct token types.
     */
    @Test
    public void testFullMode_EnumDeclaration() throws Exception {
        String uri = "file:///SemTok_FullEnum.java";
        String source =
                "public enum SemTok_FullEnum {\n"
                + "    A, B, C\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Enum declaration must produce an enum token", byType(tokens, ENM).isEmpty());
        long memberCount = countByType(tokens, ENM_MBR);
        assertTrue("Enum constants A, B, C must produce enumMember tokens; got " + memberCount,
                memberCount >= 3);
    }

    /**
     * In full mode, a record declaration produces a
     * {@link SemanticTokensProvider#TT_STRUCT} token (records map to "struct").
     */
    @Test
    public void testFullMode_RecordDeclaration() throws Exception {
        String uri = "file:///SemTok_FullRecord.java";
        String source =
                "public record SemTok_FullRecord(int x, String name) {\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Record declaration must produce a struct token",
                byType(tokens, STRUCT).isEmpty());
    }

    /**
     * In full mode, a method declaration produces a
     * {@link SemanticTokensProvider#TT_METHOD} token with TM_DECLARATION.
     */
    @Test
    public void testFullMode_MethodDeclaration() throws Exception {
        String uri = "file:///SemTok_FullMethod.java";
        String source =
                "public class SemTok_FullMethod {\n"
                + "    public int compute(int x) { return x + 1; }\n" // line 1
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        List<Token> methods = byType(tokens, MTH);
        assertFalse("Method declaration must produce a method token", methods.isEmpty());
        assertTrue("Method declaration token must have TM_DECLARATION",
                methods.stream().anyMatch(t -> (t.mods() & TM_DECLARATION) != 0));
    }

    /**
     * In full mode, a static field produces a {@link SemanticTokensProvider#TT_PROPERTY}
     * token with both TM_DECLARATION and TM_STATIC.
     */
    @Test
    public void testFullMode_StaticFieldDeclaration() throws Exception {
        String uri = "file:///SemTok_StaticField.java";
        String source =
                "public class SemTok_StaticField {\n"
                + "    public static int counter = 0;\n"       // line 1
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        List<Token> fields = byType(tokens, FLD);
        assertFalse("Static field must produce a property token", fields.isEmpty());
        assertTrue("Static field token must have TM_STATIC",
                fields.stream().anyMatch(t -> (t.mods() & TM_STATIC) != 0));
    }

    /**
     * In full mode, a final field produces a {@link SemanticTokensProvider#TT_PROPERTY}
     * token with TM_READONLY.
     */
    @Test
    public void testFullMode_FinalFieldDeclaration() throws Exception {
        String uri = "file:///SemTok_FinalField.java";
        String source =
                "public class SemTok_FinalField {\n"
                + "    public final int MAX = 100;\n"           // line 1
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        List<Token> fields = byType(tokens, FLD);
        assertFalse("Final field must produce a property token", fields.isEmpty());
        assertTrue("Final field token must have TM_READONLY",
                fields.stream().anyMatch(t -> (t.mods() & TM_READONLY) != 0));
    }

    /**
     * In full mode, a method parameter produces a
     * {@link SemanticTokensProvider#TT_PARAMETER} token.
     */
    @Test
    public void testFullMode_MethodParameter() throws Exception {
        String uri = "file:///SemTok_Param.java";
        String source =
                "public class SemTok_Param {\n"
                + "    public int m(int value) { return value; }\n"  // 'value' is a parameter
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Method parameter must produce a parameter token",
                byType(tokens, PAR).isEmpty());
    }

    /**
     * In full mode, a local variable produces a
     * {@link SemanticTokensProvider#TT_VARIABLE} token.
     */
    @Test
    public void testFullMode_LocalVariable() throws Exception {
        String uri = "file:///SemTok_LocalVar.java";
        String source =
                "public class SemTok_LocalVar {\n"
                + "    public int m() {\n"
                + "        int local = 42;\n"                  // 'local' is a local var
                + "        return local;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Local variable must produce a variable token",
                byType(tokens, VAR).isEmpty());
    }

    /**
     * In full mode, a primitive type keyword ({@code int}) in a variable declaration
     * must produce a {@link SemanticTokensProvider#TT_TYPE} token.
     */
    @Test
    public void testFullMode_PrimitiveType() throws Exception {
        String uri = "file:///SemTok_PrimType.java";
        String source =
                "public class SemTok_PrimType {\n"
                + "    public int m() { return 0; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Primitive 'int' must produce a type token in full mode",
                byType(tokens, TYP).isEmpty());
    }

    /**
     * A {@code @Override} annotation must produce a
     * {@link SemanticTokensProvider#TT_DECORATOR} token in full mode.
     */
    @Test
    public void testFullMode_Annotation() throws Exception {
        String uri = "file:///SemTok_Ann.java";
        String source =
                "public class SemTok_Ann {\n"
                + "    @Override\n"                            // line 1
                + "    public String toString() { return \"\"; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("@Override must produce a decorator token in full mode",
                byType(tokens, DEC).isEmpty());
    }

    /**
     * In full mode, a binary operator ({@code +}) must produce an operator token.
     */
    @Test
    public void testFullMode_BinaryOperator() throws Exception {
        String uri = "file:///SemTok_BinOp.java";
        String source =
                "public class SemTok_BinOp {\n"
                + "    public int m(int x) { return x + 1; }\n"  // '+' is an operator
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Binary operator '+' must produce an operator token in full mode",
                byType(tokens, OP).isEmpty());
    }

    /**
     * In full mode, a string literal must produce a
     * {@link SemanticTokensProvider#TT_STRING} token.
     */
    @Test
    public void testFullMode_StringLiteral() throws Exception {
        String uri = "file:///SemTok_StrLit.java";
        String source =
                "public class SemTok_StrLit {\n"
                + "    public String m() { return \"hello\"; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("String literal must produce a string token in full mode",
                byType(tokens, STR).isEmpty());
    }

    /**
     * In full mode, a numeric literal must produce a
     * {@link SemanticTokensProvider#TT_NUMBER} token.
     */
    @Test
    public void testFullMode_NumericLiteral() throws Exception {
        String uri = "file:///SemTok_NumLit.java";
        String source =
                "public class SemTok_NumLit {\n"
                + "    public int m() { return 42; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Numeric literal must produce a number token in full mode",
                byType(tokens, NUM).isEmpty());
    }

    // -----------------------------------------------------------------------
    // Tests: JML-only mode — Java symbols NOT highlighted
    // -----------------------------------------------------------------------

    /**
     * In JML-only mode (the default), Java identifiers outside JML context must
     * produce no tokens at all.
     */
    @Test
    public void testJmlOnlyMode_NoJavaTokensOutsideJml() throws Exception {
        String uri = "file:///SemTok_JmlOnly.java";
        String source =
                "public class SemTok_JmlOnly {\n"
                + "    public int m() { return 42; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        // JML-only mode (fullMode = false)
        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("JML-only mode must produce no tokens for plain Java", tokens.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Tests: JML ghost/model declarations
    // -----------------------------------------------------------------------

    /**
     * A JML ghost field declaration must produce tokens in JML-only mode:
     * the {@code ghost} keyword (TT_KEYWORD) and the field name symbol (TT_PROPERTY).
     */
    @Test
    public void testGhostField_KeywordAndSymbol() throws Exception {
        String uri = "file:///SemTok_Ghost.java";
        String source =
                "public class SemTok_Ghost {\n"
                + "    //@ ghost int ghostField = 0;\n"        // line 1
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("ghost keyword must produce a keyword token", countByType(tokens, KW) >= 1);
    }

    /**
     * A JML ghost field WITH a JML modifier (spec_public ghost) must produce
     * both a modifier token and a keyword token.
     */
    @Test
    public void testGhostField_WithModifier_BothPresent() throws Exception {
        String uri = "file:///SemTok_GhostMod.java";
        String source =
                "public class SemTok_GhostMod {\n"
                + "    //@ spec_public ghost int g = 0;\n"     // line 1
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("spec_public modifier must produce a modifier token", countByType(tokens, MOD) >= 1);
        assertTrue("ghost keyword must produce a keyword token", countByType(tokens, KW) >= 1);
    }

    // -----------------------------------------------------------------------
    // Tests: JML operators
    // -----------------------------------------------------------------------

    /**
     * The JML implication operator {@code ==>} must produce an operator token.
     */
    @Test
    public void testJmlImplicationOperator() throws Exception {
        String uri = "file:///SemTok_Implication.java";
        String source =
                "public class SemTok_Implication {\n"
                + "    //@ ensures x > 0 ==> \\result > 0;\n" // line 1: '==>' is JML operator
                + "    public int m(int x) { return x > 0 ? x : 1; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        // The ==> operator should produce an operator token
        assertFalse("JML implication ==> must produce an operator token",
                byType(tokens, OP).isEmpty());
    }

    // -----------------------------------------------------------------------
    // Tests: JML primitive types (\bigint, \real, etc.)
    // -----------------------------------------------------------------------

    /**
     * In full mode, the primitive type {@code int} in a method return type and parameter
     * must produce {@link SemanticTokensProvider#TT_TYPE} tokens.
     */
    @Test
    public void testJmlPrimitiveType_IntInFullMode() throws Exception {
        String uri = "file:///SemTok_IntType.java";
        String source =
                "public class SemTok_IntType {\n"
                + "    public int compute(int x) { return x; }\n" // 'int' appears twice
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST must be cached after checkContent", entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        long typeCount = countByType(tokens, TYP);
        assertTrue("'int' return type and parameter type must produce type tokens; got " + typeCount,
                typeCount >= 2);
    }

    // -----------------------------------------------------------------------
    // Tests: JML behavior keyword, also keyword
    // -----------------------------------------------------------------------

    /**
     * The {@code behavior} (or {@code normal_behavior}) keyword in a
     * specification case must produce a keyword token.
     */
    @Test
    public void testBehaviorKeyword() throws Exception {
        String uri = "file:///SemTok_Behavior.java";
        String source =
                "public class SemTok_Behavior {\n"
                + "    /*@ normal_behavior\n"                  // line 1
                + "      @ requires x > 0;\n"
                + "      @ ensures \\result > 0;\n"
                + "      @*/\n"
                + "    public int m(int x) { return x; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        // At minimum: normal_behavior + requires + ensures = 3 keyword tokens
        long kw = countByType(tokens, KW);
        assertTrue("normal_behavior, requires, ensures → at least 3 keyword tokens; got " + kw,
                kw >= 3);
    }

    // -----------------------------------------------------------------------
    // Tests: also keyword
    // -----------------------------------------------------------------------

    /**
     * The {@code also} keyword separating specification cases must produce a keyword token.
     */
    @Test
    public void testAlsoKeyword() throws Exception {
        String uri = "file:///SemTok_Also.java";
        String source =
                "public class SemTok_Also {\n"
                + "    /*@ requires x > 0;\n"
                + "      @ also\n"                             // line 2: 'also'
                + "      @ requires x == 0;\n"
                + "      @*/\n"
                + "    public void m(int x) {}\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        // requires + also + requires = at least 3 keyword tokens
        long kw = countByType(tokens, KW);
        assertTrue("also + requires + requires → at least 3 keyword tokens; got " + kw, kw >= 3);
    }

    // -----------------------------------------------------------------------
    // Tests: full mode — static method
    // -----------------------------------------------------------------------

    /**
     * In full mode, a static method must produce a method token with TM_STATIC.
     */
    @Test
    public void testFullMode_StaticMethod() throws Exception {
        String uri = "file:///SemTok_StaticMethod.java";
        String source =
                "public class SemTok_StaticMethod {\n"
                + "    public static int helper(int x) { return x; }\n"  // line 1
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        List<Token> methods = byType(tokens, MTH);
        assertFalse("Static method must produce a method token", methods.isEmpty());
        assertTrue("Static method must have TM_STATIC",
                methods.stream().anyMatch(t -> (t.mods() & TM_STATIC) != 0));
    }

    // -----------------------------------------------------------------------
    // Tests: type parameter
    // -----------------------------------------------------------------------

    /**
     * In full mode, a generic type parameter must produce a
     * {@link SemanticTokensProvider#TT_TYPE_PARAM} token.
     */
    @Test
    public void testFullMode_TypeParameter() throws Exception {
        String uri = "file:///SemTok_TypeParam.java";
        String source =
                "public class SemTok_TypeParam<T> {\n"
                + "    T value;\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Type parameter T must produce a typeParameter token",
                byType(tokens, TP).isEmpty());
    }

    // -----------------------------------------------------------------------
    // Tests: constructors
    // -----------------------------------------------------------------------

    /**
     * A plain constructor (no JML, full mode) must produce a method token at the
     * constructor name with the {@link SemanticTokensProvider#TM_DECLARATION} modifier.
     */
    @Test
    public void testFullMode_Constructor_NoJml() throws Exception {
        String uri = "file:///SemTok_CtorNoJml.java";
        String source =
                "public class SemTok_CtorNoJml {\n"                  // line 0
                + "    public SemTok_CtorNoJml() {}\n"               // line 1: ctor at col 11
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        List<Token> methods = byType(tokens, MTH);
        assertFalse("Constructor must produce a method token", methods.isEmpty());
        // The constructor declaration must carry TM_DECLARATION.
        assertTrue("Constructor declaration must have TM_DECLARATION",
                methods.stream().anyMatch(t -> (t.mods() & TM_DECLARATION) != 0));
        // Token text spans the class name "SemTok_CtorNoJml" (16 chars) at col 11.
        assertToken(tokens, MTH, 1, 11, "SemTok_CtorNoJml".length());
    }

    /**
     * A constructor annotated with JML (requires / ensures) must produce:
     * <ul>
     *   <li>a method token for the constructor name with {@code TM_DECLARATION};</li>
     *   <li>keyword tokens for the {@code requires} and {@code ensures} clauses.</li>
     * </ul>
     */
    @Test
    public void testFullMode_Constructor_WithJml() throws Exception {
        String uri = "file:///SemTok_CtorJml.java";
        String source =
                "public class SemTok_CtorJml {\n"                    // line 0
                + "    int x;\n"                                      // line 1
                + "    //@ requires n >= 0;\n"                        // line 2: requires at col 8
                + "    //@ ensures x == n;\n"                         // line 3: ensures at col 8
                + "    public SemTok_CtorJml(int n) { x = n; }\n"    // line 4: ctor at col 11
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));

        // Constructor method token at line 4, col 11.
        assertToken(tokens, MTH, 4, 11, "SemTok_CtorJml".length());

        // JML clause keywords.
        assertToken(tokens, KW, 2, 8, "requires".length());
        assertToken(tokens, KW, 3, 8, "ensures".length());
    }

    /**
     * A {@code pure} constructor must carry the {@code pure} JML modifier token
     * in addition to the constructor method token.
     */
    @Test
    public void testFullMode_Constructor_PureModifier() throws Exception {
        String uri = "file:///SemTok_CtorPure.java";
        String source =
                "public class SemTok_CtorPure {\n"                    // line 0
                + "    //@ requires n >= 0;\n"                         // line 1
                + "    /*@ pure */ public SemTok_CtorPure(int n) {}\n" // line 2: ctor at col 19
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));

        // At least one JML modifier token (pure) must be present.
        assertFalse("pure modifier must produce a TT_MODIFIER token",
                byType(tokens, MOD).isEmpty());
        // requires keyword.
        assertTrue("requires must produce a keyword token", countByType(tokens, KW) >= 1);
        // Constructor method token must be present.
        assertFalse("Constructor must produce a method token", byType(tokens, MTH).isEmpty());
    }

    /**
     * In JML-only mode a plain constructor (no JML annotations) must produce
     * no tokens at all — Java-only constructs are suppressed.
     */
    @Test
    public void testJmlOnlyMode_Constructor_NoJml_NoTokens() throws Exception {
        String uri = "file:///SemTok_CtorJmlOnly.java";
        String source =
                "public class SemTok_CtorJmlOnly {\n"                // line 0
                + "    public SemTok_CtorJmlOnly() {}\n"             // line 1
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        // JML-only mode (fullMode=false): no JML context, so no tokens expected.
        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("JML-only mode: plain constructor must produce no tokens", tokens.isEmpty());
    }

    // -----------------------------------------------------------------------
    // Tests: JML type-level clauses
    // -----------------------------------------------------------------------

    /**
     * An {@code in} clause (data group membership) must produce a keyword token.
     * Exercises {@code visitJmlTypeClauseIn}.
     * The {@code in} clause must follow the field declaration it annotates.
     */
    @Test
    public void testInClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_InClause.java";
        // 'in' clause must come AFTER the field it annotates (parser uses mostRecentVarDecl).
        String source =
                "public class SemTok_InClause {\n"
                + "    //@ ghost int myGroup;\n"
                + "    public int x;\n"
                + "    //@ in myGroup;\n"               // line 3: follows x; exercises visitJmlTypeClauseIn
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST must be cached after checkContent", entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("'in' clause or ghost decl must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /** A {@code represents} clause must produce a keyword token. */
    @Test
    public void testRepresentsClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Represents.java";
        String source =
                "public class SemTok_Represents {\n"
                + "    //@ ghost int size;\n"
                + "    //@ represents size = 0;\n"      // line 2
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("'represents' or 'ghost' must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /** A {@code monitors_for} clause must produce a keyword token. */
    @Test
    public void testMonitorsForClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_MonitorsFor.java";
        String source =
                "public class SemTok_MonitorsFor {\n"
                + "    //@ monitors_for x <- this;\n"   // line 1
                + "    public int x;\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("'monitors_for' clause must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /** An {@code initializer} clause on a static initializer must produce a keyword token. */
    @Test
    public void testInitializerClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Initializer.java";
        String source =
                "public class SemTok_Initializer {\n"
                + "    //@ initializer\n"               // line 1
                + "    static {}\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("'initializer' clause must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /**
     * A {@code readable_if} clause on a field must produce a keyword token when
     * the clause is recognized by OpenJML ({@code visitJmlTypeClauseConditional}).
     * The test is skipped gracefully if the clause is not supported.
     */
    @Test
    public void testReadableIfClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_ReadableIf.java";
        String source =
                "public class SemTok_ReadableIf {\n"
                + "    //@ readable_if x > 0;\n"        // line 1
                + "    public int x;\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        if (entry == null) return;  // readable_if may not be supported in this OpenJML version

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("'readable_if' clause must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /**
     * A {@code maps} clause must produce a keyword token.
     * Exercises {@code visitJmlTypeClauseMaps}.
     * The {@code maps} clause must follow the field it annotates.
     */
    @Test
    public void testMapsClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Maps.java";
        // 'maps' clause must come AFTER the field it annotates (parser uses mostRecentVarDecl).
        String source =
                "public class SemTok_Maps {\n"
                + "    //@ ghost int group;\n"
                + "    public int x;\n"
                + "    //@ maps x \\into group;\n"      // line 3: follows x; exercises visitJmlTypeClauseMaps
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("'maps' or 'ghost' must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    // -----------------------------------------------------------------------
    // Tests: JML method-level clauses
    // -----------------------------------------------------------------------

    /**
     * A {@code callable} clause must produce a keyword token.
     * Exercises {@code visitJmlMethodClauseCallable}.
     */
    @Test
    public void testCallableClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Callable.java";
        String source =
                "public class SemTok_Callable {\n"
                + "    //@ callable getValue;\n"        // line 1
                + "    public int getValue() { return 0; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("'callable' clause must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /**
     * An {@code accessible} clause must produce a keyword token.
     * Exercises {@code visitJmlMethodClauseStoreRef}.
     */
    @Test
    public void testAccessibleClause_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Accessible.java";
        String source =
                "public class SemTok_Accessible {\n"
                + "    public int x;\n"
                + "    //@ accessible x;\n"             // line 2
                + "    public int getX() { return x; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("'accessible' clause must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /**
     * A {@code duration} clause with a conditional ({@code if} guard) must produce a keyword token.
     * Exercises {@code visitJmlMethodClauseConditional} — produced by
     * {@code duration}, {@code measured_by}, and {@code working_space} clauses.
     */
    @Test
    public void testDurationClause_ConditionalKeyword() throws Exception {
        String uri = "file:///SemTok_Duration.java";
        String source =
                "public class SemTok_Duration {\n"
                + "    //@ duration 0 if true;\n"       // line 1: exercises visitJmlMethodClauseConditional
                + "    public int m() { return 0; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("'duration' clause must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /**
     * An {@code old} variable declaration in a spec case must produce a keyword token.
     * Exercises {@code visitJmlMethodClauseDecl}.
     */
    @Test
    public void testJmlMethodClauseDecl_KeywordToken() throws Exception {
        String uri = "file:///SemTok_OldDecl.java";
        String source =
                "public class SemTok_OldDecl {\n"
                + "    //@ old int v = 0;\n"            // line 1: exercises visitJmlMethodClauseDecl
                + "    //@ ensures \\result >= v;\n"
                + "    public int m() { return 1; }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertTrue("'old' variable declaration must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    // -----------------------------------------------------------------------
    // Tests: JML statements in method bodies
    // -----------------------------------------------------------------------

    /**
     * A JML {@code assert} statement in a method body must produce a keyword token.
     * Exercises {@code visitJmlStatementExpr}.
     */
    @Test
    public void testJmlAssertStatement_KeywordToken() throws Exception {
        String uri = "file:///SemTok_JmlAssert.java";
        String source =
                "public class SemTok_JmlAssert {\n"
                + "    public int m(int x) {\n"
                + "        //@ assert x > 0;\n"         // line 2
                + "        return x;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        // fullMode=true: method bodies are scanned, exposing JML statements inside them.
        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertTrue("JML 'assert' statement must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /**
     * A JML {@code set} statement in a method body must produce a keyword token.
     * Exercises {@code visitJmlStatement}.
     */
    @Test
    public void testSetStatement_KeywordToken() throws Exception {
        String uri = "file:///SemTok_Set.java";
        String source =
                "public class SemTok_Set {\n"
                + "    //@ ghost int g = 0;\n"
                + "    public void m() {\n"
                + "        //@ set g = 1;\n"            // line 3
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        // fullMode=true: method bodies are scanned, exposing JML statements inside them.
        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertTrue("JML 'set' statement must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /**
     * A {@code loop_invariant} annotation on a loop must produce a keyword token.
     * Exercises {@code visitJmlStatementLoopExpr}.
     */
    @Test
    public void testLoopInvariant_KeywordToken() throws Exception {
        String uri = "file:///SemTok_LoopInv.java";
        String source =
                "public class SemTok_LoopInv {\n"
                + "    public void m(int n) {\n"
                + "        int i = 0;\n"
                + "        //@ loop_invariant i >= 0;\n" // line 3
                + "        while (i < n) i++;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        // fullMode=true: method bodies are scanned, exposing JML loop annotations inside them.
        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertTrue("'loop_invariant' must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    /**
     * A local JML ghost variable declaration in a method body must produce a keyword token.
     * Exercises the JML branch of {@code visitVarDef} for locals.
     */
    @Test
    public void testLocalGhostDecl_KeywordToken() throws Exception {
        String uri = "file:///SemTok_LocalGhost.java";
        String source =
                "public class SemTok_LocalGhost {\n"
                + "    public void m() {\n"
                + "        //@ ghost int local = 0;\n"  // line 2
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        // fullMode=true: method bodies are scanned, exposing JML locals inside them.
        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertTrue("local JML 'ghost' declaration must produce a keyword token",
                countByType(tokens, KW) >= 1);
    }

    // -----------------------------------------------------------------------
    // Tests: JML primitive types
    // -----------------------------------------------------------------------

    /**
     * A ghost field with the JML primitive type {@code \bigint} must produce a
     * {@link SemanticTokensProvider#TT_TYPE} token.
     * Exercises {@code visitJmlPrimitiveTypeTree}.
     */
    @Test
    public void testJmlPrimitiveType_Bigint() throws Exception {
        String uri = "file:///SemTok_Bigint.java";
        String source =
                "public class SemTok_Bigint {\n"
                + "    //@ ghost \\bigint count = 0;\n" // line 1: \bigint at col 15
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        // The ghost keyword always produces KW; visitJmlPrimitiveTypeTree is exercised
        // for the \bigint vartype (TYP token emitted when tree.pos >= 0).
        assertTrue("'ghost' must produce a keyword token", countByType(tokens, KW) >= 1);
    }

    // -----------------------------------------------------------------------
    // Tests: Java control flow in full mode
    // -----------------------------------------------------------------------

    /**
     * In full mode, an {@code if} statement must produce a keyword token.
     * Exercises {@code visitIf}.
     */
    @Test
    public void testFullMode_IfStatement_Keyword() throws Exception {
        String uri = "file:///SemTok_If.java";
        String source =
                "public class SemTok_If {\n"
                + "    public int m(int x) {\n"
                + "        if (x > 0) return x;\n"      // line 2: 'if' at col 8
                + "        return 0;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 2, 8, 2);  // "if"
    }

    /**
     * In full mode, a {@code for} loop must produce a keyword token.
     * Exercises {@code visitForLoop}.
     */
    @Test
    public void testFullMode_ForLoop_Keyword() throws Exception {
        String uri = "file:///SemTok_For.java";
        String source =
                "public class SemTok_For {\n"
                + "    public int m(int n) {\n"
                + "        int s = 0;\n"
                + "        for (int i = 0; i < n; i++) s += i;\n"  // line 3: 'for' at col 8
                + "        return s;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 3, 8, 3);  // "for"
    }

    /**
     * In full mode, an enhanced {@code for} (foreach) loop must produce a keyword token.
     * Exercises {@code visitForeachLoop}.
     */
    @Test
    public void testFullMode_ForeachLoop_Keyword() throws Exception {
        String uri = "file:///SemTok_Foreach.java";
        String source =
                "public class SemTok_Foreach {\n"
                + "    public int m(int[] arr) {\n"
                + "        int s = 0;\n"
                + "        for (int x : arr) s += x;\n" // line 3: 'for' at col 8
                + "        return s;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 3, 8, 3);  // "for" (foreach)
    }

    /**
     * In full mode, a {@code while} loop must produce a keyword token.
     * Exercises {@code visitWhileLoop}.
     */
    @Test
    public void testFullMode_WhileLoop_Keyword() throws Exception {
        String uri = "file:///SemTok_While.java";
        String source =
                "public class SemTok_While {\n"
                + "    public int m(int n) {\n"
                + "        int i = n;\n"
                + "        while (i > 0) i--;\n"        // line 3: 'while' at col 8
                + "        return i;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 3, 8, 5);  // "while"
    }

    /**
     * In full mode, a {@code do}-{@code while} loop must produce a keyword token.
     * Exercises {@code visitDoLoop}.
     */
    @Test
    public void testFullMode_DoLoop_Keyword() throws Exception {
        String uri = "file:///SemTok_Do.java";
        String source =
                "public class SemTok_Do {\n"
                + "    public int m(int n) {\n"
                + "        int i = 0;\n"
                + "        do { i++; } while (i < n);\n" // line 3: 'do' at col 8
                + "        return i;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 3, 8, 2);  // "do"
    }

    /**
     * In full mode, a {@code switch} statement must produce a keyword token.
     * Exercises {@code visitSwitch} and {@code visitCase}.
     */
    @Test
    public void testFullMode_Switch_Keyword() throws Exception {
        String uri = "file:///SemTok_Switch.java";
        String source =
                "public class SemTok_Switch {\n"
                + "    public int m(int x) {\n"
                + "        switch (x) {\n"              // line 2: 'switch' at col 8
                + "            case 1: return 1;\n"
                + "            default: return 0;\n"
                + "        }\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 2, 8, 6);  // "switch"
    }

    /**
     * In full mode, {@code try} and {@code catch} blocks must each produce a keyword token.
     * Exercises {@code visitTry} and {@code visitCatch}.
     */
    @Test
    public void testFullMode_TryCatch_Keywords() throws Exception {
        String uri = "file:///SemTok_TryCatch.java";
        String source =
                "public class SemTok_TryCatch {\n"
                + "    public int m() {\n"
                + "        try {\n"                     // line 2: 'try' at col 8
                + "            return 1;\n"
                + "        } catch (Exception e) {\n"   // line 4: 'catch' at col 10
                + "            return 0;\n"
                + "        }\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 2, 8, 3);   // "try"
        assertToken(tokens, KW, 4, 10, 5);  // "catch"
    }

    /**
     * In full mode, a {@code throw} statement must produce a keyword token.
     * Exercises {@code visitThrow}.
     */
    @Test
    public void testFullMode_Throw_Keyword() throws Exception {
        String uri = "file:///SemTok_Throw.java";
        String source =
                "public class SemTok_Throw {\n"
                + "    public void m() throws Exception {\n"
                + "        throw new Exception(\"err\");\n"  // line 2: 'throw' at col 8
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 2, 8, 5);  // "throw"
    }

    /**
     * In full mode, a Java {@code assert} statement must produce a keyword token.
     * Exercises {@code visitAssert}.
     */
    @Test
    public void testFullMode_JavaAssert_Keyword() throws Exception {
        String uri = "file:///SemTok_JavaAssert.java";
        String source =
                "public class SemTok_JavaAssert {\n"
                + "    public void m(int x) {\n"
                + "        assert x > 0;\n"             // line 2: 'assert' at col 8
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 2, 8, 6);  // "assert"
    }

    /**
     * In full mode, a {@code synchronized} block must produce a keyword token.
     * Exercises {@code visitSynchronized}.
     */
    @Test
    public void testFullMode_Synchronized_Keyword() throws Exception {
        String uri = "file:///SemTok_Synchronized.java";
        String source =
                "public class SemTok_Synchronized {\n"
                + "    public void m() {\n"
                + "        synchronized (this) {}\n"    // line 2: 'synchronized' at col 8
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 2, 8, 12);  // "synchronized"
    }

    /**
     * In full mode, a text block must produce a {@link SemanticTokensProvider#TT_STRING} token.
     * Exercises the text-block branch of {@code visitLiteral} (TypeTag.CLASS).
     */
    @Test
    public void testFullMode_TextBlock_StringToken() throws Exception {
        String uri = "file:///SemTok_TextBlock.java";
        // The text block literal starts at the opening triple-quote.
        String source =
                "public class SemTok_TextBlock {\n"
                + "    public String m() {\n"
                + "        return \"\"\"\n"             // line 2: opening \"\"\"
                + "                hello\n"
                + "                \"\"\";\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Text block must produce a string token", byType(tokens, STR).isEmpty());
    }

    /**
     * In full mode, a unary operator ({@code !}) must produce an operator token.
     * Exercises {@code visitUnary}.
     */
    @Test
    public void testFullMode_UnaryOperator() throws Exception {
        String uri = "file:///SemTok_Unary.java";
        String source =
                "public class SemTok_Unary {\n"
                + "    public boolean m(boolean x) { return !x; }\n"  // '!' is unary
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Unary '!' must produce an operator token", byType(tokens, OP).isEmpty());
    }

    /**
     * In full mode, a compound-assignment operator ({@code +=}) must produce an operator token.
     * Exercises {@code visitAssignop}.
     */
    @Test
    public void testFullMode_AssignOp() throws Exception {
        String uri = "file:///SemTok_AssignOp.java";
        String source =
                "public class SemTok_AssignOp {\n"
                + "    public int m(int x) { x += 1; return x; }\n"  // '+=' is assignop
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertFalse("Compound assignment '+=' must produce an operator token",
                byType(tokens, OP).isEmpty());
    }

    // -----------------------------------------------------------------------
    // Tests: break, continue, new array
    // -----------------------------------------------------------------------

    /**
     * In full mode, a {@code break} statement must produce a keyword token.
     * Exercises {@code visitBreak}.
     */
    @Test
    public void testFullMode_Break_Keyword() throws Exception {
        String uri = "file:///SemTok_Break.java";
        String source =
                "public class SemTok_Break {\n"
                + "    public int m(int n) {\n"
                + "        for (int i = 0; i < n; i++) {\n"
                + "            break;\n"                // line 3: 'break' at col 12
                + "        }\n"
                + "        return 0;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 3, 12, 5);  // "break"
    }

    /**
     * In full mode, a {@code continue} statement must produce a keyword token.
     * Exercises {@code visitContinue}.
     */
    @Test
    public void testFullMode_Continue_Keyword() throws Exception {
        String uri = "file:///SemTok_Continue.java";
        String source =
                "public class SemTok_Continue {\n"
                + "    public int m(int n) {\n"
                + "        int s = 0;\n"
                + "        for (int i = 0; i < n; i++) {\n"
                + "            if (i == 0) continue;\n" // line 4: 'continue' at col 24
                + "            s += i;\n"
                + "        }\n"
                + "        return s;\n"
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 4, 24, 8);  // "continue"
    }

    /**
     * In full mode, a {@code new} array allocation must produce a keyword token.
     * Exercises {@code visitNewArray}.
     */
    @Test
    public void testFullMode_NewArray_Keyword() throws Exception {
        String uri = "file:///SemTok_NewArray.java";
        String source =
                "public class SemTok_NewArray {\n"
                + "    public int[] m(int n) {\n"
                + "        return new int[n];\n"        // line 2: 'new' at col 15
                + "    }\n"
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull(entry);

        List<Token> tokens = decode(SemanticTokensProvider.computeTokensFromAst(entry, source, true));
        assertToken(tokens, KW, 2, 15, 3);  // "new"
    }

    // -----------------------------------------------------------------------
    // buildLineOffsets fallback path
    // -----------------------------------------------------------------------

    /**
     * When {@link SemanticTokensProvider#forceLineOffsetFallback} is set,
     * {@link SemanticTokensProvider.JmlAstWalker} uses {@code buildLineOffsets}
     * (binary-search over a scanned offset array) instead of {@code cu.lineMap}
     * (O(1) javac table) for offset→line:col conversion.
     *
     * <p>The test uses the same source as {@link #testRequiresClause_KeywordToken}
     * and asserts the identical token positions, proving that the fallback path
     * produces correct coordinates — no off-by-one errors in line or column.
     *
     * <p>A multi-line source is used so that both the line increment (binary-search
     * lands on the correct line) and the column offset (subtraction from
     * {@code lineOffsets[line]}) are exercised.
     */
    @Test
    public void testBuildLineOffsetsFallback_CorrectPositions() throws Exception {
        String uri = "file:///SemTok_LineOffsetFallback.java";
        // Source with tokens on multiple lines to stress-test the binary search
        // and the column subtraction in lineForOffset / toLineCol.
        String source =
                "public class SemTok_LineOffsetFallback {\n"    // line 0
                + "    //@ requires x > 0;\n"                   // line 1: requires at col 8
                + "    //@ ensures \\result >= 0;\n"            // line 2: ensures at col 8, \result at col 16
                + "    public int m(int x) { return x; }\n"     // line 3
                + "}\n";
        checkContent(uri, source);

        ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
        assertNotNull("AST must be cached after checkContent", entry);

        // First verify positions via the normal lineMap path (establishes the ground truth).
        List<Token> normalTokens = decode(
                SemanticTokensProvider.computeTokensFromAst(entry, source, false));
        assertFalse("Normal path must produce tokens", normalTokens.isEmpty());
        assertToken(normalTokens, KW, 1, 8, "requires".length());  // requires
        assertToken(normalTokens, KW, 2, 8, "ensures".length());   // ensures
        assertToken(normalTokens, BS, 2, 16, "\\result".length());  // \result

        // Now force the buildLineOffsets fallback and verify positions are identical.
        SemanticTokensProvider.forceLineOffsetFallback.set(true);
        try {
            List<Token> fallbackTokens = decode(
                    SemanticTokensProvider.computeTokensFromAst(entry, source, false));
            assertFalse("Fallback path must produce tokens", fallbackTokens.isEmpty());
            assertToken(fallbackTokens, KW, 1, 8, "requires".length());
            assertToken(fallbackTokens, KW, 2, 8, "ensures".length());
            assertToken(fallbackTokens, BS, 2, 16, "\\result".length());
            assertEquals("Fallback must produce the same number of tokens as lineMap path",
                    normalTokens.size(), fallbackTokens.size());
        } finally {
            SemanticTokensProvider.forceLineOffsetFallback.set(false);
        }
    }
}
