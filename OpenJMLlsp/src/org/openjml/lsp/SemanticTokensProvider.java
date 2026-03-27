package org.openjml.lsp;

import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.tree.JCTree.*;
import org.eclipse.lsp4j.SemanticTokens;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Computes semantic tokens for JML constructs in Java source files.
 *
 * <p>Two strategies are available:
 * <ul>
 *   <li>{@link #computeTokensFromAst} — AST-walker approach using a cached
 *       {@link ASTCache.Entry}.  Only tokens at genuine JML AST nodes are
 *       highlighted, so identifiers that happen to share a name with a JML
 *       keyword (e.g. a field named {@code requires}) are not falsely coloured.
 *       Additionally, boolean literals ({@code true}/{@code false}/{@code null})
 *       and primitive type keywords ({@code int}, {@code boolean}, …) inside
 *       JML expressions are coloured — the Java tokeniser does not handle
 *       these inside comment regions.</li>
 *   <li>{@link #computeTokens} — regex-based fallback used when no cached AST
 *       is available (e.g. before the first {@code --check} run completes).</li>
 * </ul>
 *
 * <p>Only tokens inside JML comment regions are highlighted — Java syntax is
 * already handled by VS Code's built-in Java grammar.  Three token types are
 * produced:
 * <ul>
 *   <li>{@code keyword} (index 0) — JML clause and modifier keywords such as
 *       {@code requires}, {@code ensures}, {@code invariant}, {@code pure},
 *       {@code ghost}, {@code model}, etc.</li>
 *   <li>{@code macro} (index 1) — JML backslash-expressions such as
 *       {@code \result}, {@code \old}, {@code \forall}, {@code \exists},
 *       {@code \nothing}, etc.</li>
 *   <li>{@code variable} (index 2) — identifiers and field references inside
 *       JML expression contexts.  Emitting an explicit token here overrides
 *       TM4E's regex-based keyword coloring at that position, ensuring that a
 *       Java identifier whose name coincides with a JML keyword (e.g. a field
 *       named {@code requires}) is not falsely highlighted as a keyword.</li>
 * </ul>
 *
 * <p>JML regions recognised by the regex fallback:
 * <ul>
 *   <li>Single-line: {@code //@ ...} (any amount of leading whitespace)</li>
 *   <li>Block: {@code /*@ ... @*}{@code /} — multiline; each line is scanned</li>
 * </ul>
 */
public class SemanticTokensProvider {

    /** Index of the {@code keyword} token type in the legend. */
    public static final int TT_KEYWORD = 0;

    /** Index of the {@code macro} token type in the legend. */
    public static final int TT_MACRO    = 1;

    /**
     * Index of the {@code variable} token type in the legend.
     *
     * <p>Used for identifier and field-access nodes inside JML expression
     * contexts.  Emitting this type at a position causes
     * {@code StyleRangeMerger} (LSP4E) to override TM4E's coloring at that
     * position, preventing false keyword highlighting when an identifier
     * happens to share a name with a JML clause keyword.
     */
    public static final int TT_VARIABLE = 2;

    /** Token types registered in the server capabilities legend (order matters). */
    public static final List<String> TOKEN_TYPES     = List.of("keyword", "macro", "variable");

    /** No token modifiers used. */
    public static final List<String> TOKEN_MODIFIERS = List.of();

    // -----------------------------------------------------------------------
    // JML keyword sets (used by the regex fallback)
    // -----------------------------------------------------------------------
    //
    // These lists live in JmlKeywords — edit them there.

    /** JML clause and modifier keywords (plain word-boundary matched). */
    private static final Set<String> JML_KEYWORDS = JmlKeywords.JML_KEYWORDS;

    /**
     * JML backslash-expression keywords (the part AFTER the backslash).
     * Matched as {@code \word}.
     */
    private static final Set<String> JML_BACKSLASH = JmlKeywords.JML_BACKSLASH;

    // -----------------------------------------------------------------------
    // Patterns (regex fallback)
    // -----------------------------------------------------------------------

    private static final Pattern BACKSLASH_WORD = Pattern.compile("\\\\([a-zA-Z_][a-zA-Z0-9_]*)");
    private static final Pattern PLAIN_WORD     = Pattern.compile("[a-zA-Z_][a-zA-Z0-9_]*");

    // Detects the start of a JML line comment: optional whitespace then //@
    private static final Pattern JML_LINE_START = Pattern.compile("^(\\s*)//(@+)");
    // Detects the start of a JML block comment: optional whitespace then /*@
    private static final Pattern JML_BLOCK_START = Pattern.compile("^(\\s*)/\\*(@+)");

    // -----------------------------------------------------------------------
    // AST-walker approach
    // -----------------------------------------------------------------------

    /**
     * Compute semantic tokens by walking the attributed JML AST.
     *
     * <p>Only genuine JML keyword tokens are highlighted — identifiers that
     * share a name with a JML keyword but are used as Java identifiers are
     * not falsely coloured.  Boolean literals and primitive type keywords
     * appearing inside JML expressions are also highlighted.
     *
     * @param entry  cached AST entry for the file
     * @param source the full Java source text (used for offset→line:col mapping)
     * @return LSP-encoded semantic tokens (delta-encoded 5-integer tuples)
     */
    public static SemanticTokens computeTokensFromAst(ASTCache.Entry entry, String source) {
        int[] lineOffsets = buildLineOffsets(source);
        List<int[]> tokens = new ArrayList<>();  // each: [line, col, len, type]
        new JmlAstWalker(source, lineOffsets, tokens).scan(entry.ast());
        // Sort by (line, col) in case AST order differs from source order.
        tokens.sort(Comparator.comparingInt((int[] t) -> t[0]).thenComparingInt(t -> t[1]));
        // Debug: log every token so we can see which semantic category each word gets.
        String[] TYPE_NAMES = { "keyword", "macro", "variable" };
        for (int[] tok : tokens) {
            int off = lineOffsets[tok[0]] + tok[1];
            String text = source.substring(off, Math.min(off + tok[2], source.length()));
            String typeName = (tok[3] >= 0 && tok[3] < TYPE_NAMES.length) ? TYPE_NAMES[tok[3]] : String.valueOf(tok[3]);
            System.err.println("[semtok] " + typeName + " '" + text + "' L" + (tok[0]+1) + ":" + tok[1]);
        }
        return deltaEncode(tokens);
    }

    /**
     * Build an array where {@code lineOffsets[i]} is the character offset of
     * the start of line {@code i} (0-based) in {@code source}.
     */
    private static int[] buildLineOffsets(String source) {
        int count = 1;
        for (int i = 0; i < source.length(); i++) {
            if (source.charAt(i) == '\n') count++;
        }
        int[] offsets = new int[count];
        offsets[0] = 0;
        int idx = 1;
        for (int i = 0; i < source.length(); i++) {
            if (source.charAt(i) == '\n') offsets[idx++] = i + 1;
        }
        return offsets;
    }

    /** Convert sorted [line, col, len, type] tuples to the LSP delta-encoded format. */
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
            data.add(0);       // token modifiers (none)
            prevLine = tok[0];
            prevCol  = tok[1];
        }
        return new SemanticTokens(data);
    }

    // -----------------------------------------------------------------------
    // JmlAstWalker — emits tokens by walking the JML AST
    // -----------------------------------------------------------------------

    private static class JmlAstWalker extends JmlTreeScanner {

        private final String   source;
        private final int[]    lineOffsets;
        private final List<int[]> tokens;
        /** Depth inside JML spec expression context (> 0 means inside a JML clause body). */
        private int jmlDepth = 0;

        JmlAstWalker(String source, int[] lineOffsets, List<int[]> tokens) {
            super(null);  // null context: Log.instance() calls are guarded by null check
            this.source      = source;
            this.lineOffsets = lineOffsets;
            this.tokens      = tokens;
        }

        // ---- token emission ------------------------------------------------

        /**
         * Emit a token starting at character offset {@code pos}.
         *
         * <p>The token type is inferred from the first character: a backslash
         * produces {@link SemanticTokensProvider#TT_MACRO}, anything else
         * produces {@link SemanticTokensProvider#TT_KEYWORD}.  The token
         * length is determined by scanning word characters (letters, digits,
         * underscores) from {@code pos}, including the leading backslash if
         * present.
         */
        private void emitAt(int pos) {
            if (pos < 0 || pos >= source.length()) return;
            char first = source.charAt(pos);
            int type = (first == '\\') ? TT_MACRO : TT_KEYWORD;
            emitAt(pos, type);
        }

        private void emitAt(int pos, int type) {
            if (pos < 0 || pos >= source.length()) return;
            int start = pos;
            // Include leading backslash in the token span.
            int end = (source.charAt(pos) == '\\') ? pos + 1 : pos;
            while (end < source.length() && isWordChar(source.charAt(end))) end++;
            int len = end - start;
            if (len == 0) return;
            int line = lineForOffset(start);
            int col  = start - lineOffsets[line];
            tokens.add(new int[]{line, col, len, type});
        }

        private static boolean isWordChar(char c) {
            return Character.isLetterOrDigit(c) || c == '_';
        }

        /**
         * Find the source offset of {@code word} as a complete identifier token,
         * scanning forward from {@code searchFrom} up to 512 characters.
         * Returns -1 if not found.
         */
        private int findWordAfter(int searchFrom, String word) {
            int limit = Math.min(source.length() - word.length(), searchFrom + 512);
            for (int i = searchFrom; i <= limit; i++) {
                char c = source.charAt(i);
                if (!isWordChar(c)) continue;
                // start of a word — check if it matches
                if (source.startsWith(word, i)) {
                    int endPos = i + word.length();
                    if (endPos >= source.length() || !isWordChar(source.charAt(endPos))) {
                        return i;
                    }
                }
                // skip rest of current word
                while (i < limit && isWordChar(source.charAt(i))) i++;
            }
            return -1;
        }

        /** Binary-search {@code lineOffsets} to find the 0-based line for {@code offset}. */
        private int lineForOffset(int offset) {
            int lo = 0, hi = lineOffsets.length - 1;
            while (lo < hi) {
                int mid = (lo + hi + 1) / 2;
                if (lineOffsets[mid] <= offset) lo = mid;
                else hi = mid - 1;
            }
            return lo;
        }

        // ---- JmlMethodClause overrides -------------------------------------

        @Override
        public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
            emitClause(tree);
            jmlDepth++; super.visitJmlMethodClauseExpr(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseConditional(JmlMethodClauseConditional tree) {
            emitClause(tree);
            jmlDepth++; super.visitJmlMethodClauseConditional(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree) {
            emitClause(tree);
            jmlDepth++; super.visitJmlMethodClauseDecl(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseCallable(JmlMethodClauseCallable tree) {
            emitClause(tree);
            jmlDepth++; super.visitJmlMethodClauseCallable(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseBehaviors(JmlMethodClauseBehaviors tree) {
            emitClause(tree);
            jmlDepth++; super.visitJmlMethodClauseBehaviors(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseInvariants(JmlMethodClauseInvariants tree) {
            emitClause(tree);
            jmlDepth++; super.visitJmlMethodClauseInvariants(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseSignals(JmlMethodClauseSignals tree) {
            emitClause(tree);
            jmlDepth++; super.visitJmlMethodClauseSignals(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly tree) {
            emitClause(tree);
            jmlDepth++; super.visitJmlMethodClauseSigOnly(tree); jmlDepth--;
        }

        @Override
        public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef tree) {
            emitClause(tree);
            jmlDepth++; super.visitJmlMethodClauseStoreRef(tree); jmlDepth--;
        }

        private void emitClause(JmlMethodClause tree) {
            emitAt(tree.pos, TT_KEYWORD);
        }

        // ---- JmlTypeClause overrides ---------------------------------------

        @Override
        public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree) {
            emitTypeClause(tree);
            jmlDepth++; super.visitJmlTypeClauseExpr(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint tree) {
            emitTypeClause(tree);
            jmlDepth++; super.visitJmlTypeClauseConstraint(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseConditional(JmlTypeClauseConditional tree) {
            emitTypeClause(tree);
            jmlDepth++; super.visitJmlTypeClauseConditional(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseIn(JmlTypeClauseIn tree) {
            emitTypeClause(tree);
            jmlDepth++; super.visitJmlTypeClauseIn(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer tree) {
            emitTypeClause(tree);
            // children are initializer specs — scanned by super
        }

        @Override
        public void visitJmlTypeClauseMaps(JmlTypeClauseMaps tree) {
            emitTypeClause(tree);
            jmlDepth++; super.visitJmlTypeClauseMaps(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor tree) {
            emitTypeClause(tree);
            jmlDepth++; super.visitJmlTypeClauseMonitorsFor(tree); jmlDepth--;
        }

        @Override
        public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) {
            emitTypeClause(tree);
            jmlDepth++; super.visitJmlTypeClauseRepresents(tree); jmlDepth--;
        }

        private void emitTypeClause(JmlTypeClause tree) {
            emitAt(tree.pos, TT_KEYWORD);
        }

        // ---- JmlSpecificationCase ------------------------------------------

        @Override
        public void visitJmlSpecificationCase(JmlSpecificationCase tree) {
            // Emit 'also' / 'implies_that' if present (alsoPos >= 0 means set).
            if (tree.alsoPos >= 0) emitAt(tree.alsoPos, TT_KEYWORD);
            // Emit the case keyword: 'behavior', 'normal_behavior', etc.
            if (tree.token != null && tree.pos >= 0) emitAt(tree.pos, TT_KEYWORD);
            super.visitJmlSpecificationCase(tree);
        }

        // ---- JML expressions -----------------------------------------------

        @Override
        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr tree) {
            // e.g. \forall, \exists, \sum, \product, \num_of, \let
            emitAt(tree.pos, TT_MACRO);
            jmlDepth++; super.visitJmlQuantifiedExpr(tree); jmlDepth--;
        }

        @Override
        public void visitJmlSingleton(JmlSingleton tree) {
            // e.g. \result, \nothing, \everything, \not_specified
            emitAt(tree.pos, TT_MACRO);
            // no children
        }

        @Override
        public void visitJmlMethodInvocation(JmlMethodInvocation that) {
            // e.g. \old(expr), \fresh(expr), \typeof(expr) — startpos is the '\'
            if (that.startpos >= 0) emitAt(that.startpos, TT_MACRO);
            jmlDepth++; super.visitJmlMethodInvocation(that); jmlDepth--;
        }

        @Override
        public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree tree) {
            // JML-specific primitive types like \TYPE, \bigint
            emitAt(tree.pos, TT_MACRO);
            // no children
        }

        @Override
        public void visitJmlStoreRefKeyword(JmlStoreRefKeyword tree) {
            // e.g. \nothing, \everything (store-ref context)
            emitAt(tree.pos, TT_MACRO);
            // no children
        }

        // ---- JML statements ------------------------------------------------

        @Override
        public void visitJmlStatementExpr(JmlStatementExpr tree) {
            // e.g. assume, assert, unreachable
            emitAt(tree.pos, TT_KEYWORD);
            jmlDepth++; super.visitJmlStatementExpr(tree); jmlDepth--;
        }

        @Override
        public void visitJmlStatement(JmlStatement tree) {
            // e.g. set, debug
            emitAt(tree.pos, TT_KEYWORD);
            scan(tree.statement);
        }

        // ---- JML ghost/model variable and method declarations ---------------

        /** Java modifier keywords that may appear in JML ghost/model declarations. */
        private static final Set<String> JAVA_MODIFIERS = JmlKeywords.JAVA_MODIFIERS;

        /**
         * Emit tokens for all modifier keywords preceding {@code typePos}.
         *
         * <p>JML-specific modifiers (ghost, model, pure, …) are taken from the
         * {@link JmlModifiers#jmlmods} list, which records exact token positions.
         * Java modifier keywords (public, static, …) are found by scanning the
         * source text between {@code mods.pos} and {@code typePos}.
         */
        private void emitJmlDeclarationMods(JCModifiers mods, int typePos) {
            if (mods == null || mods.pos < 0) return;

            // 1. JML-specific modifier tokens with exact positions.
            if (mods instanceof JmlModifiers jmlMods) {
                for (JmlToken tok : jmlMods.jmlmods) {
                    if (tok.pos >= 0) {
                        int len = tok.endPos - tok.pos;
                        if (len > 0) {
                            int line = lineForOffset(tok.pos);
                            int col  = tok.pos - lineOffsets[line];
                            tokens.add(new int[]{line, col, len, TT_KEYWORD});
                        }
                    }
                }
            }

            // 2. Java modifier keywords: scan source in [mods.pos, typePos).
            int pos = mods.pos;
            while (pos < typePos && pos < source.length()) {
                char c = source.charAt(pos);
                if (Character.isLetter(c) || c == '_') {
                    int end = pos;
                    while (end < typePos && end < source.length() && isWordChar(source.charAt(end))) end++;
                    String word = source.substring(pos, end);
                    if (JAVA_MODIFIERS.contains(word)) {
                        int line = lineForOffset(pos);
                        int col  = pos - lineOffsets[line];
                        tokens.add(new int[]{line, col, word.length(), TT_KEYWORD});
                    }
                    pos = end;
                } else {
                    pos++;
                }
            }
        }

        /**
         * JML ghost/model field declarations: color modifiers and type.
         *
         * <p>These are regular {@link JmlVariableDecl} nodes with the JML bit set
         * (e.g. {@code //@ ghost static int x}).  The variable type is colored by
         * incrementing {@code jmlDepth} so that {@link #visitTypeIdent} fires.
         */
        @Override
        public void visitVarDef(JCVariableDecl tree) {
            if (tree instanceof JmlVariableDecl jmlVar && jmlVar.isJML()) {
                int typePos = jmlVar.vartype != null ? jmlVar.vartype.pos : jmlVar.pos;
                emitJmlDeclarationMods(jmlVar.mods, typePos);
                jmlDepth++;
                super.visitVarDef(tree);
                jmlDepth--;
                // Emit the declared name as a variable token (JCVariableDecl.name is
                // a Name field, not a tree node, so visitIdent is never called for it).
                if (jmlVar.name != null && !jmlVar.name.isEmpty()) {
                    int namePos = jmlVar.namePosition >= 0
                            ? jmlVar.namePosition
                            : findWordAfter(
                                jmlVar.vartype != null
                                    ? jmlVar.vartype.pos + jmlVar.vartype.toString().length()
                                    : typePos,
                                jmlVar.name.toString());
                    if (namePos >= 0) emitAt(namePos, TT_VARIABLE);
                }
            } else {
                super.visitVarDef(tree);
            }
        }

        /**
         * JML ghost/model method declarations: color modifiers and return type.
         *
         * <p>Incrementing {@code jmlDepth} also colors parameter types via
         * {@link #visitTypeIdent}.
         */
        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            if (tree instanceof JmlMethodDecl jmlMethod && jmlMethod.isJML()) {
                int typePos = jmlMethod.restype != null ? jmlMethod.restype.pos : jmlMethod.pos;
                emitJmlDeclarationMods(jmlMethod.mods, typePos);
                jmlDepth++;
                super.visitMethodDef(tree);
                jmlDepth--;
                // Emit the declared method name as a variable token.
                if (jmlMethod.name != null && !jmlMethod.name.isEmpty()) {
                    int namePos = jmlMethod.namePosition >= 0
                            ? jmlMethod.namePosition
                            : findWordAfter(
                                jmlMethod.restype != null
                                    ? jmlMethod.restype.pos + jmlMethod.restype.toString().length()
                                    : typePos,
                                jmlMethod.name.toString());
                    if (namePos >= 0) emitAt(namePos, TT_VARIABLE);
                }
            } else {
                super.visitMethodDef(tree);
            }
        }

        // ---- Java literals and type identifiers inside JML context ---------

        @Override
        public void visitLiteral(JCLiteral tree) {
            if (jmlDepth > 0) {
                // Color 'true', 'false', and 'null' — the Java tokeniser does not
                // produce semantic tokens for literals inside comment regions.
                TypeTag tag = tree.typetag;
                if (tag == TypeTag.BOOLEAN || tag == TypeTag.BOT) {
                    emitAt(tree.pos, TT_KEYWORD);
                }
            }
            // no children
        }

        @Override
        public void visitTypeIdent(JCPrimitiveTypeTree tree) {
            if (jmlDepth > 0) {
                // Color 'int', 'long', 'boolean', etc. inside JML expressions
                // (e.g. the type in \forall int i; ...).
                emitAt(tree.pos, TT_KEYWORD);
            }
            // no children
        }

        // ---- Identifiers inside JML expressions ----------------------------

        /**
         * Emit a {@link SemanticTokensProvider#TT_VARIABLE} token for any
         * simple identifier that appears inside a JML expression context
         * ({@code jmlDepth > 0}).
         *
         * <p>This overrides TM4E's regex-based keyword coloring for positions
         * where the identifier's name coincides with a JML clause keyword.
         * For example, in {@code //@ requires requires > 0;} the second
         * {@code requires} is a {@code JCIdent} and receives a {@code variable}
         * token, while the first one is emitted as {@code keyword} by
         * {@link #visitJmlMethodClauseExpr}.
         */
        @Override
        public void visitIdent(JCIdent tree) {
            if (jmlDepth > 0 && tree.pos >= 0) {
                emitAt(tree.pos, TT_VARIABLE);
            }
            // no children
        }

        /**
         * When a field-access expression (e.g. {@code this.field}) appears
         * inside a JML expression, emit a {@link SemanticTokensProvider#TT_VARIABLE}
         * token for the field-name part.
         *
         * <p>The position of the field name is approximated by searching
         * backward from the node's end position for the last dot and reading
         * the word that follows it.  If the position cannot be determined,
         * only the receiver is scanned (which handles {@code this} / the
         * qualifier identifiers via {@link #visitIdent}).
         */
        @Override
        public void visitSelect(JCFieldAccess tree) {
            if (jmlDepth > 0 && tree.pos >= 0 && tree.name != null) {
                // The AST pos of JCFieldAccess points to the start of the
                // whole expression.  Locate the field name by scanning for
                // the last '.' in [tree.pos, end) and emitting from the char
                // after it.  We read at most name.length() + 1 chars after '.'
                // to stay safe.
                String name = tree.name.toString();
                // Scan forward from tree.pos to find the position of 'name'
                // after the last '.'.  Walk the source looking for .<name>
                // followed by a non-word character or end-of-input.
                int searchFrom = tree.pos;
                int namePos = -1;
                int limit = Math.min(source.length() - name.length(), searchFrom + 512);
                for (int i = searchFrom; i <= limit; i++) {
                    if (source.charAt(i) == '.' && i + 1 + name.length() <= source.length()) {
                        int after = i + 1;
                        if (source.startsWith(name, after)) {
                            int endOfName = after + name.length();
                            if (endOfName >= source.length() || !isWordChar(source.charAt(endOfName))) {
                                namePos = after;
                                // keep scanning: we want the LAST '.<name>' occurrence
                                // (handles chains like a.b.c where all parts share a name —
                                //  rare, but keep searching for correctness)
                            }
                        }
                    }
                }
                if (namePos >= 0) {
                    emitAt(namePos, TT_VARIABLE);
                }
            }
            // Scan the receiver (selected) — it may be a JCIdent or another
            // JCFieldAccess; both emit tokens via their own visit methods
            // since jmlDepth is already > 0 in this context.
            super.visitSelect(tree);
        }
    }

    // -----------------------------------------------------------------------
    // Regex-based fallback
    // -----------------------------------------------------------------------

    /**
     * Compute semantic tokens for {@code source} using regex matching.
     *
     * <p>This fallback is used when no attributed AST is available.  It may
     * produce false positives for identifiers that share a name with a JML
     * keyword, but is much faster than a full compilation pass.
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
                if (line.contains("@*/") || line.contains("*/")) {
                    inBlockJml = false;
                }
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

            // 1. Backslash-expressions → TT_MACRO
            Matcher bsm = BACKSLASH_WORD.matcher(content);
            while (bsm.find()) {
                if (JML_BACKSLASH.contains(bsm.group(1))) {
                    lineTokens.add(new int[]{ base + bsm.start(), bsm.end() - bsm.start(), TT_MACRO });
                }
            }

            // 2. Plain JML keywords → TT_KEYWORD (skip columns already claimed)
            java.util.Set<Integer> claimed = new java.util.HashSet<>();
            for (int[] t : lineTokens) {
                for (int c = t[0]; c < t[0] + t[1]; c++) claimed.add(c);
            }
            Matcher pm = PLAIN_WORD.matcher(content);
            while (pm.find()) {
                int col = base + pm.start();
                if (!claimed.contains(col) && JML_KEYWORDS.contains(pm.group())) {
                    lineTokens.add(new int[]{ col, pm.end() - pm.start(), TT_KEYWORD });
                }
            }

            lineTokens.sort(Comparator.comparingInt(t -> t[0]));
            for (int[] tok : lineTokens) {
                allTokens.add(new int[]{ lineIdx, tok[0], tok[1], tok[2] });
            }
        }

        return deltaEncode(allTokens);
    }
}
