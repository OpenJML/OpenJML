package org.openjml.lsp;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.*;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Position;
import org.eclipse.lsp4j.SemanticTokens;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Computes semantic tokens for Java+JML source files.
 *
 * <p>Two strategies are available:
 * <ul>
 *   <li>{@link #computeTokensFromAst} — AST-walker approach using a cached
 *       {@link ASTCache.Entry}.  Provides precise, false-positive-free highlighting.
 *       Supports two modes:
 *       <ul>
 *         <li><b>JML-only</b> ({@code fullMode=false}): only JML constructs and Java
 *             constructs appearing within JML contexts (e.g. model method bodies)
 *             are highlighted.  Intended for co-existence with the Red Hat Java
 *             extension, which handles Java coloring independently.</li>
 *         <li><b>Full</b> ({@code fullMode=true}): all Java and JML constructs are
 *             highlighted.  Intended for standalone use without a Java extension.</li>
 *       </ul>
 *   </li>
 *   <li>{@link #computeTokens} — regex-based fallback used before the first
 *       {@code --check} completes.  JML-region detection only.</li>
 * </ul>
 *
 * <h3>Position conventions</h3>
 * <p>The walker uses {@code cu.lineMap} (populated during lexing, always present
 * after a {@code --check} pass) for O(1) offset→line:col conversion.  If for any
 * reason {@code lineMap} is null the implementation falls back to a scanned
 * {@code lineOffsets[]} array and logs a warning.
 *
 * <h3>Backslash token type</h3>
 * <p>All JML backslash expressions ({@code \result}, {@code \old}, {@code \forall},
 * etc.) use the type index named by {@link #BACKSLASH_TOKEN_TYPE}.  Changing that
 * one constant (and rebuilding) switches all of them at once without touching the
 * legend, since both {@code "function"} and {@code "macro"} are declared in the
 * legend.
 */
public class SemanticTokensProvider {

    // -----------------------------------------------------------------------
    // Token type indices (must match TOKEN_TYPES order)
    // -----------------------------------------------------------------------

    public static final int TT_NAMESPACE   =  0;
    public static final int TT_CLASS       =  1;
    public static final int TT_INTERFACE   =  2;
    public static final int TT_ENUM        =  3;
    /** Records map to {@code struct} — distinguished from plain classes. */
    public static final int TT_STRUCT      =  4;
    public static final int TT_TYPE_PARAM  =  5;
    /** Primitives ({@code int}, {@code boolean}, …) and JML built-in types
     *  ({@code \bigint}, {@code \real}, {@code \locset}, …). */
    public static final int TT_TYPE        =  6;
    public static final int TT_PARAMETER   =  7;
    /** Local variables. */
    public static final int TT_VARIABLE    =  8;
    /** Fields (instance and static). */
    public static final int TT_PROPERTY    =  9;
    public static final int TT_ENUM_MEMBER = 10;
    public static final int TT_METHOD      = 11;
    /** Currently used for JML backslash tokens (see {@link #BACKSLASH_TOKEN_TYPE}). */
    public static final int TT_FUNCTION    = 12;
    /**
     * Reserved — not currently emitted.
     * <p>Both {@code "function"} (index 12) and {@code "macro"} (index 13) are
     * declared in the legend so that {@link #BACKSLASH_TOKEN_TYPE} can be switched
     * from one to the other by changing a single constant without a legend change
     * (which would require a server restart and client reconnection).
     */
    public static final int TT_MACRO       = 13;
    public static final int TT_KEYWORD     = 14;
    /** JML modifiers: {@code pure}, {@code spec_public}, {@code nullable}, etc. */
    public static final int TT_MODIFIER    = 15;
    /** Java and JML annotations: {@code @Override}, {@code @NonNull}, etc. */
    public static final int TT_DECORATOR   = 16;
    /** Reserved — JML comment delimiters ({@code //@}, {@code /*@}) are not in the AST. */
    public static final int TT_COMMENT     = 17;
    /** String literals and text blocks. */
    public static final int TT_STRING      = 18;
    /** Numeric and character literals. */
    public static final int TT_NUMBER      = 19;
    /** Java and JML operators. */
    public static final int TT_OPERATOR    = 20;

    /**
     * The token type used for all JML backslash expressions
     * ({@code \result}, {@code \old}, {@code \forall}, {@code \nothing}, etc.).
     *
     * <p>Currently {@link #TT_FUNCTION}.  To reclassify all backslash tokens as
     * {@code macro}, change this constant to {@link #TT_MACRO} — no other change
     * is needed, since both token types are declared in the legend.
     *
     * <p>POSITION CONVENTION: the AST position for backslash tokens
     * ({@link JmlSingleton#pos}, {@link JmlQuantifiedExpr#pos},
     * {@link JmlMethodInvocation#startpos}) is the offset of the leading {@code \}.
     * This is a parser-established invariant relied on by {@link JmlAstWalker}.
     */
    public static final int BACKSLASH_TOKEN_TYPE = TT_FUNCTION;

    /** Token types registered in the server capabilities legend (order is significant). */
    public static final List<String> TOKEN_TYPES = List.of(
        "namespace",     //  0
        "class",         //  1
        "interface",     //  2
        "enum",          //  3
        "struct",        //  4  records
        "typeParameter", //  5
        "type",          //  6  primitives + JML built-in types
        "parameter",     //  7
        "variable",      //  8
        "property",      //  9  fields
        "enumMember",    // 10
        "method",        // 11
        "function",      // 12  backslash tokens (see BACKSLASH_TOKEN_TYPE)
        "macro",         // 13  reserved; see BACKSLASH_TOKEN_TYPE comment
        "keyword",       // 14
        "modifier",      // 15  JML modifiers
        "decorator",     // 16  annotations
        "comment",       // 17  reserved; JML delimiters not in AST
        "string",        // 18
        "number",        // 19
        "operator"       // 20
    );

    // -----------------------------------------------------------------------
    // Token modifier bit masks (must match TOKEN_MODIFIERS order)
    // -----------------------------------------------------------------------

    public static final int TM_DECLARATION    =   1;  // bit 0
    public static final int TM_DEFINITION     =   2;  // bit 1
    public static final int TM_READONLY       =   4;  // bit 2
    public static final int TM_STATIC         =   8;  // bit 3
    public static final int TM_DEPRECATED     =  16;  // bit 4
    public static final int TM_ABSTRACT       =  32;  // bit 5
    // bits 6-8 unused (async, modification, documentation)
    public static final int TM_DEFAULT_LIB    = 512;  // bit 9

    /** Token modifiers registered in the legend (order is significant). */
    public static final List<String> TOKEN_MODIFIERS = List.of(
        "declaration",   // bit 0 = 1
        "definition",    // bit 1 = 2
        "readonly",      // bit 2 = 4
        "static",        // bit 3 = 8
        "deprecated",    // bit 4 = 16
        "abstract",      // bit 5 = 32
        "async",         // bit 6 = 64    (unused)
        "modification",  // bit 7 = 128   (unused)
        "documentation", // bit 8 = 256   (unused)
        "defaultLibrary" // bit 9 = 512
    );

    // -----------------------------------------------------------------------
    // JML modifier keywords (emit as TT_MODIFIER, not TT_KEYWORD)
    // -----------------------------------------------------------------------

    /**
     * JML tokens from {@link JmlModifiers#jmlmods} that annotate methods, classes,
     * or fields without introducing a structural construct.  These receive
     * {@link #TT_MODIFIER} rather than {@link #TT_KEYWORD}.
     *
     * <p>Structural and behavioral keywords ({@code ghost}, {@code model},
     * {@code requires}, {@code ensures}, {@code invariant}, etc.) remain
     * {@link #TT_KEYWORD}.
     */
    private static final Set<String> JML_MODIFIER_KEYWORDS = Set.of(
        "pure", "spec_pure", "strictly_pure", "no_state", "two_state",
        "spec_public", "spec_protected",
        "non_null", "non_null_by_default", "nullable", "nullable_by_default",
        "helper", "instance", "query", "secret", "monitored", "uninitialized",
        "code_java_math", "code_safe_math", "code_bigint_math",
        "spec_java_math", "spec_safe_math", "spec_bigint_math"
    );

    private static final Set<String> JML_KEYWORDS = JmlKeywords.JML_KEYWORDS;
    private static final Set<String> JML_BACKSLASH = JmlKeywords.JML_BACKSLASH;
    private static final Set<String> JAVA_MODIFIERS = JmlKeywords.JAVA_MODIFIERS;

    // -----------------------------------------------------------------------
    // Regex patterns (fallback only)
    // -----------------------------------------------------------------------

    private static final Pattern BACKSLASH_WORD = Pattern.compile("\\\\([a-zA-Z_][a-zA-Z0-9_]*)");
    private static final Pattern PLAIN_WORD     = Pattern.compile("[a-zA-Z_][a-zA-Z0-9_]*");
    private static final Pattern JML_LINE_START  = Pattern.compile("^(\\s*)//(@+)");
    private static final Pattern JML_BLOCK_START = Pattern.compile("^(\\s*)/\\*(@+)");

    // -----------------------------------------------------------------------
    // AST-walker approach
    // -----------------------------------------------------------------------

    /**
     * Compute semantic tokens by walking the attributed JML AST.
     *
     * @param entry    cached AST entry for the file
     * @param source   full Java source text
     * @param fullMode {@code true} for Java+JML mode (emit for all Java constructs);
     *                 {@code false} for JML-only mode (emit only inside JML contexts)
     * @return LSP-encoded semantic tokens (delta-encoded 5-integer tuples)
     */
    public static SemanticTokens computeTokensFromAst(ASTCache.Entry entry,
                                                       String source,
                                                       boolean fullMode) {
        List<int[]> tokens = new ArrayList<>();
        new JmlAstWalker(entry.ast(), source, tokens, fullMode).scan(entry.ast());
        tokens.sort(Comparator.comparingInt((int[] t) -> t[0]).thenComparingInt(t -> t[1]));
        return deltaEncode(tokens);
    }

    /**
     * Compatibility overload: JML-only mode.
     * @deprecated Prefer {@link #computeTokensFromAst(ASTCache.Entry, String, boolean)}.
     */
    @Deprecated
    public static SemanticTokens computeTokensFromAst(ASTCache.Entry entry, String source) {
        return computeTokensFromAst(entry, source, false);
    }

    /** Build a line-start offset array from source (fallback when lineMap is null). */
    private static int[] buildLineOffsets(String source) {
        int count = 1;
        for (int i = 0; i < source.length(); i++) if (source.charAt(i) == '\n') count++;
        int[] offsets = new int[count];
        offsets[0] = 0;
        int idx = 1;
        for (int i = 0; i < source.length(); i++) if (source.charAt(i) == '\n') offsets[idx++] = i + 1;
        return offsets;
    }

    /** Delta-encode sorted [line, col, len, type, mods] tuples to LSP format. */
    private static SemanticTokens deltaEncode(List<int[]> tokens) {
        List<Integer> data = new ArrayList<>(tokens.size() * 5);
        int prevLine = 0, prevCol = 0;
        for (int[] tok : tokens) {
            int dLine = tok[0] - prevLine;
            int dCol  = dLine == 0 ? tok[1] - prevCol : tok[1];
            data.add(dLine);
            data.add(dCol);
            data.add(tok[2]);  // length
            data.add(tok[3]);  // token type
            data.add(tok[4]);  // token modifiers
            prevLine = tok[0];
            prevCol  = tok[1];
        }
        return new SemanticTokens(data);
    }

    // -----------------------------------------------------------------------
    // JmlAstWalker
    // -----------------------------------------------------------------------

    private static class JmlAstWalker extends JmlTreeScanner {

        private final JmlCompilationUnit cu;
        private final Position.LineMap   lineMap;       // null → use lineOffsets
        private final int[]              lineOffsets;   // null → use lineMap
        private final String             source;
        private final List<int[]>        tokens;        // [line, col, len, type, mods]
        private final boolean            fullMode;

        /**
         * Depth inside a JML spec expression context.  Greater than zero when the
         * walker is visiting nodes that appear inside a JML clause body, a JML
         * ghost/model declaration, or a model method body.  In JML-only mode tokens
         * are only emitted for Java constructs (operators, literals, identifiers)
         * when this depth is positive.
         */
        private int jmlDepth = 0;

        JmlAstWalker(JmlCompilationUnit cu, String source, List<int[]> tokens, boolean fullMode) {
            super(null);
            this.cu       = cu;
            this.source   = source;
            this.tokens   = tokens;
            this.fullMode = fullMode;
            Position.LineMap lm = cu.lineMap;
            if (lm == null) {
                System.err.println("[SemanticTokens] WARNING: lineMap is null — " +
                    "falling back to source-scanning for offset→line:col. " +
                    "If this persists, verify that -g is passed to OpenJML invocations.");
                this.lineMap    = null;
                this.lineOffsets = buildLineOffsets(source);
            } else {
                this.lineMap    = lm;
                this.lineOffsets = null;
            }
        }

        // ---- context predicate ---------------------------------------------

        /** True when the current position is inside a JML or full-Java context. */
        private boolean inContext() { return fullMode || jmlDepth > 0; }

        // ---- position conversion -------------------------------------------

        /**
         * Convert a character offset to a [line, col] pair (both 0-based).
         *
         * <p>Prefers {@link #lineMap} (O(1)); falls back to {@link #lineOffsets}
         * scanning when lineMap is absent.
         *
         * <p>POSITION CONVENTION: for binary nodes {@code tree.pos} is the operator
         * position (established javac invariant used for diagnostics).  For JML
         * clause nodes ({@link JmlMethodClauseExpr}, {@link JmlTypeClauseExpr}, etc.)
         * {@code tree.pos} is the preferred/representative position; empirical tests
         * should verify it lands on the clause keyword rather than a preceding
         * modifier.  Use the test cases in {@code SemanticTokensTest} as regression
         * guards for this invariant.
         */
        private int[] toLineCol(int pos) {
            if (pos < 0) return null;
            if (lineMap != null) {
                int line1 = (int) lineMap.getLineNumber(pos);
                if (line1 <= 0) return null;
                int col = (int)(pos - lineMap.getStartPosition(line1));
                return new int[]{ line1 - 1, col };
            } else {
                int line = lineForOffset(pos);
                return new int[]{ line, pos - lineOffsets[line] };
            }
        }

        /** Binary-search {@code lineOffsets} for the 0-based line of {@code offset}. */
        private int lineForOffset(int offset) {
            int lo = 0, hi = lineOffsets.length - 1;
            while (lo < hi) {
                int mid = (lo + hi + 1) / 2;
                if (lineOffsets[mid] <= offset) lo = mid; else hi = mid - 1;
            }
            return lo;
        }

        // ---- token emission ------------------------------------------------

        /**
         * Emit a token of the given type and modifiers with an explicit length.
         * This is the core emission method; all other emit helpers delegate here.
         */
        private void emitToken(int pos, int type, int mods, int len) {
            if (pos < 0 || len <= 0 || pos + len > source.length()) return;
            int[] lc = toLineCol(pos);
            if (lc == null) return;
            tokens.add(new int[]{ lc[0], lc[1], len, type, mods });
        }

        /**
         * Emit a token starting at {@code pos}, inferring the length by scanning
         * word characters (letters, digits, underscores) from {@code pos}, including
         * any leading backslash for JML backslash tokens.
         */
        private void emitAt(int pos, int type, int mods) {
            if (pos < 0 || pos >= source.length()) return;
            int end = (source.charAt(pos) == '\\') ? pos + 1 : pos;
            while (end < source.length() && isWordChar(source.charAt(end))) end++;
            emitToken(pos, type, mods, end - pos);
        }

        private void emitAt(int pos, int type) { emitAt(pos, type, 0); }

        /** True for letters, digits, and underscore (Java identifier parts). */
        private static boolean isWordChar(char c) {
            return Character.isLetterOrDigit(c) || c == '_';
        }

        /**
         * Emit the appropriate semantic token for a symbol reference or declaration.
         *
         * <p>Classifies the symbol as one of: namespace, class, interface, enum,
         * struct (record), typeParameter, method, enumMember, property (field),
         * parameter, or variable, then applies relevant modifier bits.
         *
         * @param pos   source offset of the identifier token
         * @param sym   the resolved symbol (may be null — silently ignored)
         * @param isDecl true when this is the declaration site (adds TM_DECLARATION)
         */
        private void emitSymbol(int pos, Symbol sym, boolean isDecl) {
            if (sym == null || pos < 0 || pos >= source.length()) return;
            int type;
            int mods = isDecl ? TM_DECLARATION : 0;

            if (sym instanceof MethodSymbol ms) {
                type = TT_METHOD;
                long flags = ms.flags();
                if ((flags & Flags.STATIC) != 0)     mods |= TM_STATIC;
                if ((flags & Flags.ABSTRACT) != 0)   mods |= TM_ABSTRACT;
                if ((flags & Flags.DEPRECATED) != 0) mods |= TM_DEPRECATED;

            } else if (sym instanceof VarSymbol vs) {
                long flags = vs.flags();
                if ((flags & Flags.ENUM) != 0) {
                    type = TT_ENUM_MEMBER;
                } else if (vs.owner instanceof ClassSymbol) {
                    type = TT_PROPERTY;
                    if ((flags & Flags.STATIC) != 0) mods |= TM_STATIC;
                    if ((flags & Flags.FINAL)  != 0) mods |= TM_READONLY;
                } else if ((flags & Flags.PARAMETER) != 0) {
                    type = TT_PARAMETER;
                } else {
                    type = TT_VARIABLE;
                    if ((flags & Flags.FINAL) != 0) mods |= TM_READONLY;
                }
                if ((vs.flags() & Flags.DEPRECATED) != 0) mods |= TM_DEPRECATED;

            } else if (sym instanceof ClassSymbol cs) {
                long flags = cs.flags();
                if ((flags & Flags.INTERFACE) != 0)      type = TT_INTERFACE;
                else if ((flags & Flags.ENUM) != 0)      type = TT_ENUM;
                else if ((flags & Flags.RECORD) != 0)    type = TT_STRUCT;
                else                                     type = TT_CLASS;
                if ((flags & Flags.ABSTRACT) != 0
                        && (flags & Flags.INTERFACE) == 0) mods |= TM_ABSTRACT;
                if ((flags & Flags.DEPRECATED) != 0)     mods |= TM_DEPRECATED;

            } else if (sym instanceof PackageSymbol) {
                type = TT_NAMESPACE;

            } else if (sym instanceof TypeVariableSymbol) {
                type = TT_TYPE_PARAM;

            } else {
                return;  // unrecognized symbol kind
            }

            emitAt(pos, type, mods);
        }

        /**
         * Emit {@link #TT_DECORATOR} tokens for all annotations in {@code mods}.
         * Each annotation token spans from {@code @} to the end of the annotation
         * name (not including argument parentheses).
         */
        private void emitAnnotations(JCModifiers mods) {
            if (mods == null || mods.annotations == null) return;
            for (JCAnnotation ann : mods.annotations) {
                if (ann.pos < 0 || ann.pos >= source.length()) continue;
                // Scan from '@' through the annotation name (letters, digits, '.', '_').
                int end = ann.pos + 1;
                while (end < source.length()) {
                    char c = source.charAt(end);
                    if (isWordChar(c) || c == '.') end++; else break;
                }
                emitToken(ann.pos, TT_DECORATOR, 0, end - ann.pos);
            }
        }

        /**
         * Emit tokens for any JML-specific modifiers stored in {@code mods}.
         *
         * <p>Unlike {@link #emitDeclarationMods}, this helper emits <em>only</em> the JML
         * modifier tokens (from {@link JmlModifiers#jmlmods}), without the Java modifier
         * scan.  It is called unconditionally from {@link #visitMethodDef} and
         * {@link #visitVarDef} so that JML modifiers on ordinary Java declarations are
         * always colored even in JML-only mode.
         */
        private void emitJmlMods(JCModifiers mods) {
            if (!(mods instanceof JmlModifiers jmlMods) || jmlMods.jmlmods == null) return;
            for (JmlToken tok : jmlMods.jmlmods) {
                if (tok.pos < 0) continue;
                int len = tok.endPos - tok.pos;
                if (len <= 0) continue;
                String keyword = tok.jmlclausekind != null ? tok.jmlclausekind.keyword : "";
                int tt = JML_MODIFIER_KEYWORDS.contains(keyword) ? TT_MODIFIER : TT_KEYWORD;
                emitToken(tok.pos, tt, 0, len);
            }
        }

        /**
         * Emit tokens for all modifier keywords preceding the type at {@code typePos}.
         *
         * <ul>
         *   <li>JML-specific modifiers from {@link JmlModifiers#jmlmods} are emitted
         *       using exact positions; those in {@link #JML_MODIFIER_KEYWORDS} get
         *       {@link #TT_MODIFIER}, others get {@link #TT_KEYWORD}.</li>
         *   <li>Java modifier keywords ({@code public}, {@code static}, etc.) are
         *       located by scanning the source between {@code mods.pos} and
         *       {@code typePos}; they receive {@link #TT_KEYWORD}.</li>
         * </ul>
         *
         * <p>NOTE: Java access modifier keywords are stored as bit-flags in
         * {@link JCModifiers#flags}; their source positions are not directly
         * available in the AST.  The source-scan approach here is the only way to
         * locate them without additional parser-level position fields.
         */
        private void emitDeclarationMods(JCModifiers mods, int typePos) {
            if (mods == null || mods.pos < 0) return;
            emitAnnotations(mods);

            // 1. JML-specific modifiers — exact positions from JmlModifiers.jmlmods.
            if (mods instanceof JmlModifiers jmlMods && jmlMods.jmlmods != null) {
                for (JmlToken tok : jmlMods.jmlmods) {
                    if (tok.pos < 0) continue;
                    int len = tok.endPos - tok.pos;
                    if (len <= 0) continue;
                    String keyword = tok.jmlclausekind != null ? tok.jmlclausekind.keyword : "";
                    int tt = JML_MODIFIER_KEYWORDS.contains(keyword) ? TT_MODIFIER : TT_KEYWORD;
                    emitToken(tok.pos, tt, 0, len);
                }
            }

            // 2. Java modifier keywords — scan source in [mods.pos, typePos).
            int pos = mods.pos;
            while (pos < typePos && pos < source.length()) {
                char c = source.charAt(pos);
                if (Character.isLetter(c) || c == '_') {
                    int end = pos;
                    while (end < typePos && end < source.length() && isWordChar(source.charAt(end))) end++;
                    String word = source.substring(pos, end);
                    if (JAVA_MODIFIERS.contains(word)) {
                        emitToken(pos, TT_KEYWORD, 0, word.length());
                    }
                    pos = end;
                } else {
                    pos++;
                }
            }
        }

        /**
         * Scan forward from {@code searchFrom} to find {@code word} as a complete
         * identifier token.  Returns -1 if not found within 512 characters.
         */
        private int findWordAfter(int searchFrom, String word) {
            if (searchFrom < 0) return -1;
            int limit = Math.min(source.length() - word.length(), searchFrom + 512);
            for (int i = searchFrom; i <= limit; i++) {
                if (!isWordChar(source.charAt(i))) continue;
                if (source.startsWith(word, i)) {
                    int endPos = i + word.length();
                    if (endPos >= source.length() || !isWordChar(source.charAt(endPos))) return i;
                }
                while (i < limit && isWordChar(source.charAt(i))) i++;
            }
            return -1;
        }

        /**
         * Scan the length of a string literal (including text blocks) starting at {@code pos}.
         * Returns the number of characters in the complete literal token.
         */
        private int scanStringLen(int pos) {
            if (pos >= source.length() || source.charAt(pos) != '"') return 1;
            boolean textBlock = pos + 2 < source.length()
                    && source.charAt(pos + 1) == '"' && source.charAt(pos + 2) == '"';
            if (textBlock) {
                int end = source.indexOf("\"\"\"", pos + 3);
                return end >= 0 ? end + 3 - pos : source.length() - pos;
            }
            int end = pos + 1;
            while (end < source.length() && source.charAt(end) != '"' && source.charAt(end) != '\n') {
                if (source.charAt(end) == '\\') end++;
                end++;
            }
            return (end < source.length() && source.charAt(end) == '"') ? end + 1 - pos : end - pos;
        }

        /** Scan the length of a numeric or character literal starting at {@code pos}. */
        private int scanNumberLen(int pos) {
            int end = pos;
            while (end < source.length()) {
                char c = source.charAt(end);
                if (Character.isLetterOrDigit(c) || c == '_' || c == '.' || c == '\'') end++;
                else break;
            }
            return Math.max(1, end - pos);
        }

        /** Scan the length of an operator token starting at {@code pos} (max 4 chars). */
        private int scanOperatorLen(int pos) {
            int end = pos;
            int limit = Math.min(source.length(), pos + 4);
            while (end < limit) {
                char c = source.charAt(end);
                if (isWordChar(c) || Character.isWhitespace(c)
                        || c == '(' || c == ')' || c == ';' || c == ','
                        || c == '{' || c == '}' || c == '@' || c == '"'
                        || c == '\'' || c == '/')
                    break;
                end++;
            }
            return Math.max(1, end - pos);
        }

        /** Emit a Java keyword of known length at {@code pos} when {@link #inContext()}. */
        private void emitKeyword(int pos, int len) {
            if (inContext() && pos >= 0) emitToken(pos, TT_KEYWORD, 0, len);
        }

        // ---- JmlMethodClause visitors --------------------------------------

        @Override
        public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlMethodClauseExpr(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseConditional(JmlMethodClauseConditional tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlMethodClauseConditional(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlMethodClauseDecl(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseCallable(JmlMethodClauseCallable tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlMethodClauseCallable(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseBehaviors(JmlMethodClauseBehaviors tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlMethodClauseBehaviors(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseInvariants(JmlMethodClauseInvariants tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlMethodClauseInvariants(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseSignals(JmlMethodClauseSignals tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlMethodClauseSignals(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlMethodClauseSigOnly(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlMethodClauseStoreRef(tree); jmlDepth--;
        }

        // ---- JmlTypeClause visitors ----------------------------------------

        @Override
        public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlTypeClauseExpr(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlTypeClauseConstraint(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseConditional(JmlTypeClauseConditional tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlTypeClauseConditional(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseIn(JmlTypeClauseIn tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlTypeClauseIn(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer tree) {
            emitAt(tree.pos, TT_KEYWORD);
        }

        @Override
        public void visitJmlTypeClauseMaps(JmlTypeClauseMaps tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlTypeClauseMaps(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlTypeClauseMonitorsFor(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) {
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlTypeClauseRepresents(tree); jmlDepth--;
        }

        // ---- JmlSpecificationCase ------------------------------------------

        @Override
        public void visitJmlSpecificationCase(JmlSpecificationCase tree) {
            if (tree.alsoPos >= 0) emitAt(tree.alsoPos, TT_KEYWORD);
            if (tree.token != null && tree.pos >= 0) emitAt(tree.pos, TT_KEYWORD);
            super.visitJmlSpecificationCase(tree);
        }

        // ---- JML expression nodes -----------------------------------------

        @Override
        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr tree) {
            // \forall, \exists, \sum, \product, \num_of, \let, \min, \max
            // POSITION INVARIANT: tree.pos is the '\' character.
            emitAt(tree.pos, BACKSLASH_TOKEN_TYPE);
            jmlDepth++; super.visitJmlQuantifiedExpr(tree); jmlDepth--;
        }

        @Override
        public void visitJmlSingleton(JmlSingleton tree) {
            // \result, \nothing, \everything, \not_specified, etc.
            // POSITION INVARIANT: tree.pos is the '\' character.
            emitAt(tree.pos, BACKSLASH_TOKEN_TYPE);
        }

        @Override
        public void visitJmlMethodInvocation(JmlMethodInvocation that) {
            // \old(expr), \fresh(expr), \typeof(expr), etc.
            // POSITION INVARIANT: that.startpos is the '\' character.
            if (that.startpos >= 0) emitAt(that.startpos, BACKSLASH_TOKEN_TYPE);
            jmlDepth++; super.visitJmlMethodInvocation(that); jmlDepth--;
        }

        @Override
        public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree tree) {
            // \TYPE, \bigint, \real, \locset, \datagroup, \set, \map, \seq, \array, \string
            emitAt(tree.pos, TT_TYPE);
        }

        @Override
        public void visitJmlStoreRefKeyword(JmlStoreRefKeyword tree) {
            // \nothing, \everything (store-ref context)
            emitAt(tree.pos, BACKSLASH_TOKEN_TYPE);
        }

        @Override
        public void visitJmlBinary(JmlBinary tree) {
            // JML binary operators: ==>, <==, <==>, <:, <#, <##
            // POSITION INVARIANT: tree.pos is the operator position (same convention as JCBinary).
            if (inContext() && tree.pos >= 0) {
                String opStr = (tree.op != null && tree.op.keyword != null) ? tree.op.keyword : "";
                int len = opStr.isEmpty() ? scanOperatorLen(tree.pos) : opStr.length();
                emitToken(tree.pos, TT_OPERATOR, 0, len);
            }
            jmlDepth++; super.visitJmlBinary(tree); jmlDepth--;
        }

        // ---- JML statements ------------------------------------------------

        @Override
        public void visitJmlStatementExpr(JmlStatementExpr tree) {
            // assume, assert, unreachable, reachable
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlStatementExpr(tree); jmlDepth--;
        }

        @Override
        public void visitJmlStatement(JmlStatement tree) {
            // set, debug
            emitAt(tree.pos, TT_KEYWORD);
            scan(tree.statement);
        }

        @Override
        public void visitJmlStatementLoopExpr(JmlStatementLoopExpr tree) {
            // loop_invariant, maintaining, decreasing, decreases
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlStatementLoopExpr(tree); jmlDepth--;
        }

        // ---- JML ghost/model declarations ----------------------------------

        /**
         * JML ghost/model field declarations (Pattern 1: JmlVariableDecl extends JCVariableDecl;
         * visitVarDef is called for ALL variable declarations — cast to detect JML ones).
         *
         * <p>In JML-only mode, only JML-attributed variables are highlighted.
         * In full mode, all variable declarations are highlighted.
         */
        @Override
        public void visitVarDef(JCVariableDecl tree) {
            boolean isJml = (tree instanceof JmlVariableDecl jd && jd.isJML());
            if (isJml) {
                JmlVariableDecl jmlVar = (JmlVariableDecl) tree;
                int typePos = jmlVar.vartype != null ? jmlVar.vartype.pos : jmlVar.pos;
                emitDeclarationMods(jmlVar.mods, typePos);
                jmlDepth++;
                super.visitVarDef(tree);
                jmlDepth--;
                // Emit the declared name — JCVariableDecl.name is not a tree node
                // so visitIdent is never called for it; emit manually.
                if (jmlVar.name != null && !jmlVar.name.isEmpty()) {
                    int namePos = jmlVar.namePosition >= 0
                            ? jmlVar.namePosition
                            : findWordAfter(
                                jmlVar.vartype != null
                                    ? jmlVar.vartype.pos + jmlVar.vartype.toString().length()
                                    : typePos,
                                jmlVar.name.toString());
                    if (namePos >= 0) emitSymbol(namePos, jmlVar.sym, true);
                }
            } else if (fullMode) {
                // Non-JML variable declaration in full mode.
                JmlVariableDecl jmlVar = (JmlVariableDecl) tree;
                int typePos = jmlVar.vartype != null ? jmlVar.vartype.pos : jmlVar.pos;
                emitDeclarationMods(jmlVar.mods, typePos);
                super.visitVarDef(tree);
                if (jmlVar.name != null && !jmlVar.name.isEmpty()) {
                    int namePos = jmlVar.namePosition >= 0
                            ? jmlVar.namePosition
                            : findWordAfter(typePos, jmlVar.name.toString());
                    if (namePos >= 0) emitSymbol(namePos, jmlVar.sym, true);
                }
            } else {
                // JML-only mode, non-JML variable: still emit any JML modifier tokens.
                emitJmlMods(tree.mods);
                super.visitVarDef(tree);
            }
        }

        /**
         * JML ghost/model method declarations and (in full mode) all methods.
         *
         * <p>Pattern 1: JmlMethodDecl extends JCMethodDecl; visitMethodDef is called
         * for ALL method declarations.
         */
        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            boolean isJml = (tree instanceof JmlMethodDecl jd && jd.isJML());
            if (isJml) {
                JmlMethodDecl jmlMethod = (JmlMethodDecl) tree;
                int typePos = jmlMethod.restype != null ? jmlMethod.restype.pos : jmlMethod.pos;
                emitDeclarationMods(jmlMethod.mods, typePos);
                jmlDepth++;
                super.visitMethodDef(tree);
                jmlDepth--;
                if (jmlMethod.name != null && !jmlMethod.name.isEmpty()) {
                    int namePos = jmlMethod.namePosition >= 0
                            ? jmlMethod.namePosition
                            : findWordAfter(
                                jmlMethod.restype != null
                                    ? jmlMethod.restype.pos + jmlMethod.restype.toString().length()
                                    : typePos,
                                jmlMethod.name.toString());
                    if (namePos >= 0) emitSymbol(namePos, jmlMethod.sym, true);
                }
            } else if (fullMode) {
                JmlMethodDecl jmlMethod = (JmlMethodDecl) tree;
                int typePos = jmlMethod.restype != null ? jmlMethod.restype.pos : jmlMethod.pos;
                emitDeclarationMods(jmlMethod.mods, typePos);
                super.visitMethodDef(tree);
                if (jmlMethod.name != null && !jmlMethod.name.isEmpty()
                        && !"<init>".equals(jmlMethod.name.toString())) {
                    int namePos = jmlMethod.namePosition >= 0
                            ? jmlMethod.namePosition
                            : findWordAfter(typePos, jmlMethod.name.toString());
                    if (namePos >= 0) emitSymbol(namePos, jmlMethod.sym, true);
                }
            } else {
                // JML-only mode, non-JML method: still emit any JML modifier tokens.
                emitJmlMods(tree.mods);
                super.visitMethodDef(tree);
            }
        }

        /**
         * Class declarations (Pattern 1: JmlClassDecl extends JCClassDecl).
         *
         * <p>In full mode, emits decorator tokens for annotations and recurses into
         * the class body.  In JML-only mode, only visits the class body for JML
         * type clauses (via super).
         */
        @Override
        public void visitClassDef(JCClassDecl tree) {
            if (fullMode) {
                emitAnnotations(tree.mods);
                // The class/interface/enum/record name follows tree.pos.
                // POSITION NOTE: tree.pos is set by the parser at the class-introducing
                // keyword token.  If modifiers precede it, the test
                // testClassDecl_WithModifiers_NamePositionCorrect verifies that the
                // name token is correctly located by findWordAfter.
                if (tree.name != null && !tree.name.isEmpty()) {
                    // Skip past the keyword ("class", "interface", "enum", "record")
                    // to find the name.
                    int namePos = findWordAfter(tree.pos, tree.name.toString());
                    if (namePos >= 0) emitSymbol(namePos, tree.sym, true);
                }
            }
            super.visitClassDef(tree);
        }

        // ---- Java literals and type identifiers ----------------------------

        @Override
        public void visitLiteral(JCLiteral tree) {
            if (!inContext() || tree.pos < 0) return;
            TypeTag tag = tree.typetag;
            if (tag == TypeTag.BOOLEAN || tag == TypeTag.BOT) {
                // true, false, null
                emitAt(tree.pos, TT_KEYWORD);
            } else if (tag == TypeTag.CLASS) {
                // String literal or text block
                emitToken(tree.pos, TT_STRING, 0, scanStringLen(tree.pos));
            } else if (tag == TypeTag.CHAR) {
                // Character literal
                emitToken(tree.pos, TT_NUMBER, 0, scanNumberLen(tree.pos));
            } else {
                // int, long, float, double
                emitToken(tree.pos, TT_NUMBER, 0, scanNumberLen(tree.pos));
            }
        }

        @Override
        public void visitTypeIdent(JCPrimitiveTypeTree tree) {
            if (inContext()) emitAt(tree.pos, TT_TYPE);
        }

        // ---- Identifiers and field accesses --------------------------------

        @Override
        public void visitIdent(JCIdent tree) {
            if (inContext() && tree.pos >= 0 && tree.sym != null) {
                emitSymbol(tree.pos, tree.sym, false);
            }
        }

        @Override
        public void visitSelect(JCFieldAccess tree) {
            if (inContext() && tree.pos >= 0 && tree.name != null && tree.sym != null) {
                // Locate the field name after the last '.' in the expression.
                String name = tree.name.toString();
                int namePos = -1;
                int limit = Math.min(source.length() - name.length(), tree.pos + 512);
                for (int i = tree.pos; i <= limit; i++) {
                    if (source.charAt(i) == '.' && i + 1 + name.length() <= source.length()) {
                        int after = i + 1;
                        if (source.startsWith(name, after)) {
                            int endOfName = after + name.length();
                            if (endOfName >= source.length() || !isWordChar(source.charAt(endOfName)))
                                namePos = after;
                        }
                    }
                }
                if (namePos >= 0) emitSymbol(namePos, tree.sym, false);
            }
            super.visitSelect(tree);
        }

        // ---- Java operators ------------------------------------------------

        /**
         * Java binary operators.
         *
         * <p>POSITION INVARIANT: {@code tree.pos} is the source position of the
         * binary operator token (e.g. the {@code +} in {@code a + b}).  This is an
         * established javac invariant used for diagnostic pointing; the token emitter
         * relies on it to locate the operator without a secondary source scan.
         */
        @Override
        public void visitBinary(JCBinary tree) {
            if (inContext() && tree.pos >= 0)
                emitToken(tree.pos, TT_OPERATOR, 0, scanOperatorLen(tree.pos));
            super.visitBinary(tree);
        }

        /**
         * Java unary operators (prefix and postfix: {@code !}, {@code ~},
         * {@code -}, {@code +}, {@code ++}, {@code --}).
         *
         * <p>POSITION INVARIANT: {@code tree.pos} is the operator position.
         */
        @Override
        public void visitUnary(JCUnary tree) {
            if (inContext() && tree.pos >= 0)
                emitToken(tree.pos, TT_OPERATOR, 0, scanOperatorLen(tree.pos));
            super.visitUnary(tree);
        }

        /**
         * Java compound-assignment operators ({@code +=}, {@code -=}, etc.).
         *
         * <p>POSITION INVARIANT: {@code tree.pos} is the operator position.
         */
        @Override
        public void visitAssignop(JCAssignOp tree) {
            if (inContext() && tree.pos >= 0)
                emitToken(tree.pos, TT_OPERATOR, 0, scanOperatorLen(tree.pos));
            super.visitAssignop(tree);
        }

        /**
         * Java simple assignment ({@code =}).
         *
         * <p>POSITION INVARIANT: {@code tree.pos} is the {@code =} operator position.
         */
        @Override
        public void visitAssign(JCAssign tree) {
            if (inContext() && tree.pos >= 0)
                emitToken(tree.pos, TT_OPERATOR, 0, 1);  // "=" is always 1 char
            super.visitAssign(tree);
        }

        // ---- Java annotations (decorators) ---------------------------------

        @Override
        public void visitAnnotation(JCAnnotation tree) {
            if (inContext() && tree.pos >= 0) {
                int end = tree.pos + 1;
                while (end < source.length()) {
                    char c = source.charAt(end);
                    if (isWordChar(c) || c == '.') end++; else break;
                }
                emitToken(tree.pos, TT_DECORATOR, 0, end - tree.pos);
            }
            // Do not recurse into annotation arguments — they are metadata, not code.
        }

        // ---- Java statement keywords ---------------------------------------

        @Override
        public void visitReturn(JCReturn tree) {
            emitKeyword(tree.pos, 6);  // "return"
            super.visitReturn(tree);
        }

        @Override
        public void visitIf(JCIf tree) {
            emitKeyword(tree.pos, 2);  // "if"
            // "else" position is not available in the AST — omit.
            super.visitIf(tree);
        }

        @Override
        public void visitForLoop(JCForLoop tree) {
            emitKeyword(tree.pos, 3);  // "for"
            super.visitForLoop(tree);
        }

        @Override
        public void visitForeachLoop(JCEnhancedForLoop tree) {
            emitKeyword(tree.pos, 3);  // "for"
            super.visitForeachLoop(tree);
        }

        @Override
        public void visitWhileLoop(JCWhileLoop tree) {
            emitKeyword(tree.pos, 5);  // "while"
            super.visitWhileLoop(tree);
        }

        @Override
        public void visitDoLoop(JCDoWhileLoop tree) {
            emitKeyword(tree.pos, 2);  // "do"
            super.visitDoLoop(tree);
        }

        @Override
        public void visitSwitch(JCSwitch tree) {
            emitKeyword(tree.pos, 6);  // "switch"
            super.visitSwitch(tree);
        }

        @Override
        public void visitCase(JCCase tree) {
            // "case" or "default" — scan from tree.pos to determine which.
            if (inContext() && tree.pos >= 0) {
                int end = tree.pos;
                while (end < source.length() && isWordChar(source.charAt(end))) end++;
                emitToken(tree.pos, TT_KEYWORD, 0, end - tree.pos);
            }
            super.visitCase(tree);
        }

        @Override
        public void visitTry(JCTry tree) {
            emitKeyword(tree.pos, 3);  // "try"
            // "finally" position not available in JCTry — omit.
            super.visitTry(tree);
        }

        @Override
        public void visitCatch(JCCatch tree) {
            emitKeyword(tree.pos, 5);  // "catch"
            super.visitCatch(tree);
        }

        @Override
        public void visitBreak(JCBreak tree) {
            emitKeyword(tree.pos, 5);  // "break"
        }

        @Override
        public void visitContinue(JCContinue tree) {
            emitKeyword(tree.pos, 8);  // "continue"
        }

        @Override
        public void visitThrow(JCThrow tree) {
            emitKeyword(tree.pos, 5);  // "throw"
            super.visitThrow(tree);
        }

        @Override
        public void visitAssert(JCAssert tree) {
            // Java assert (not JML assert — JML assert is visitJmlStatementExpr).
            emitKeyword(tree.pos, 6);  // "assert"
            super.visitAssert(tree);
        }

        @Override
        public void visitNewClass(JCNewClass tree) {
            emitKeyword(tree.pos, 3);  // "new"
            super.visitNewClass(tree);
        }

        @Override
        public void visitNewArray(JCNewArray tree) {
            if (tree.elemtype != null) emitKeyword(tree.pos, 3);  // "new"
            super.visitNewArray(tree);
        }

        @Override
        public void visitTypeTest(JCInstanceOf tree) {
            // "instanceof" keyword
            if (inContext() && tree.pos >= 0) emitToken(tree.pos, TT_KEYWORD, 0, 10);
            super.visitTypeTest(tree);
        }

        @Override
        public void visitSynchronized(JCSynchronized tree) {
            emitKeyword(tree.pos, 12);  // "synchronized"
            super.visitSynchronized(tree);
        }
    }

    // -----------------------------------------------------------------------
    // Regex-based fallback
    // -----------------------------------------------------------------------

    /**
     * Compute semantic tokens for {@code source} using regex matching.
     *
     * <p>This fallback is used when no attributed AST is available (before the
     * first {@code --check} completes).  It may produce false positives for
     * identifiers that share a name with a JML keyword.  Only JML regions are
     * processed; Java syntax is handled by the editor's built-in grammar.
     *
     * @param source the full Java source text
     * @return LSP-encoded semantic tokens (delta-encoded 5-integer tuples)
     */
    public static SemanticTokens computeTokens(String source) {
        List<int[]> allTokens = new ArrayList<>();
        String[] lines = source.split("\n", -1);
        boolean inBlockJml = false;

        for (int lineIdx = 0; lineIdx < lines.length; lineIdx++) {
            String line = lines[lineIdx];
            int jmlContentStart;
            boolean isJmlLine;

            if (inBlockJml) {
                isJmlLine = true;
                int col = 0;
                while (col < line.length() && Character.isWhitespace(line.charAt(col))) col++;
                if (col < line.length() && line.charAt(col) == '*') col++;
                jmlContentStart = col;
                if (line.contains("@*/") || line.contains("*/")) inBlockJml = false;
            } else {
                Matcher lm = JML_LINE_START.matcher(line);
                Matcher bm = JML_BLOCK_START.matcher(line);
                if (lm.find()) {
                    isJmlLine = true;
                    jmlContentStart = lm.end();
                } else if (bm.find()) {
                    isJmlLine = true;
                    jmlContentStart = bm.end();
                    if (!line.contains("*/")) inBlockJml = true;
                } else {
                    continue;
                }
            }

            if (!isJmlLine) continue;

            List<int[]> lineTokens = new ArrayList<>();
            String content = line.substring(Math.min(jmlContentStart, line.length()));
            int base = jmlContentStart;

            // 1. Backslash-expressions
            Matcher bsm = BACKSLASH_WORD.matcher(content);
            while (bsm.find()) {
                if (JML_BACKSLASH.contains(bsm.group(1)))
                    lineTokens.add(new int[]{ base + bsm.start(), bsm.end() - bsm.start(), BACKSLASH_TOKEN_TYPE });
            }

            // 2. Plain JML keywords (skip columns already claimed)
            Set<Integer> claimed = new HashSet<>();
            for (int[] t : lineTokens) for (int c = t[0]; c < t[0] + t[1]; c++) claimed.add(c);
            Matcher pm = PLAIN_WORD.matcher(content);
            while (pm.find()) {
                int col = base + pm.start();
                if (!claimed.contains(col) && JML_KEYWORDS.contains(pm.group())) {
                    String word = pm.group();
                    int tt = JML_MODIFIER_KEYWORDS.contains(word) ? TT_MODIFIER : TT_KEYWORD;
                    lineTokens.add(new int[]{ col, word.length(), tt });
                }
            }

            lineTokens.sort(Comparator.comparingInt(t -> t[0]));
            for (int[] tok : lineTokens)
                allTokens.add(new int[]{ lineIdx, tok[0], tok[1], tok[2], 0 });
        }

        return deltaEncode(allTokens);
    }
}
