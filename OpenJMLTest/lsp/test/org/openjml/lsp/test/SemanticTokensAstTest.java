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
}
