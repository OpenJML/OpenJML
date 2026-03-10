package org.openjml.lsp;

import org.eclipse.lsp4j.SemanticTokens;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Computes semantic tokens for JML constructs in Java source files.
 *
 * <p>Only tokens inside JML comment regions are highlighted — Java syntax is
 * already handled by VS Code's built-in Java grammar.  Two token types are
 * produced:
 * <ul>
 *   <li>{@code keyword} (index 0) — JML clause and modifier keywords such as
 *       {@code requires}, {@code ensures}, {@code invariant}, {@code pure},
 *       {@code ghost}, {@code model}, etc.</li>
 *   <li>{@code macro} (index 1) — JML backslash-expressions such as
 *       {@code \result}, {@code \old}, {@code \forall}, {@code \exists},
 *       {@code \nothing}, etc.</li>
 * </ul>
 *
 * <p>JML regions recognised:
 * <ul>
 *   <li>Single-line: {@code //@ ...} (any amount of leading whitespace)</li>
 *   <li>Block: {@code /*@ ... @*}{@code /} — multiline; each line is scanned</li>
 * </ul>
 */
public class SemanticTokensProvider {

    /** Index of the {@code keyword} token type in the legend. */
    public static final int TT_KEYWORD = 0;

    /** Index of the {@code macro} token type in the legend. */
    public static final int TT_MACRO   = 1;

    /** Token types registered in the server capabilities legend (order matters). */
    public static final List<String> TOKEN_TYPES     = List.of("keyword", "macro");

    /** No token modifiers used. */
    public static final List<String> TOKEN_MODIFIERS = List.of();

    // -----------------------------------------------------------------------
    // JML keyword sets
    // -----------------------------------------------------------------------

    /** JML clause and modifier keywords (plain word-boundary matched). */
    private static final Set<String> JML_KEYWORDS = Set.of(
        // specification clauses
        "requires", "ensures", "signals", "signals_only", "assignable",
        "modifies", "accessible", "callable", "measured_by", "captures",
        "diverges", "when", "working_space", "duration",
        "breaks", "continues", "returns",
        // type-member clauses
        "invariant", "initially", "constraint", "represents", "axiom",
        "readable", "writable", "monitors_for",
        // case combinators
        "also", "implies_that", "for_example", "example",
        // declaration modifiers
        "pure", "ghost", "model", "spec_public", "spec_protected", "spec_private",
        "non_null", "nullable", "helper", "instance", "query", "secret",
        "no_state", "two_state", "monitored", "uninitialized",
        "code_java_math", "code_safe_math", "code_bigint_math",
        "spec_java_math", "spec_safe_math", "spec_bigint_math",
        // statement / expression keywords
        "loop_invariant", "maintaining", "decreasing", "decreases",
        "assume", "assert", "set", "debug", "hence_by", "unreachable",
        "reachable", "in", "maps",
        // quantifier words (JML uses these without backslash too)
        "forall", "exists", "min", "max", "sum", "product", "num_of",
        "let", "old", "pre", "result", "not_modified"
    );

    /**
     * JML backslash-expression keywords (the part AFTER the backslash).
     * Matched as {@code \word}.
     */
    private static final Set<String> JML_BACKSLASH = Set.of(
        "result", "old", "pre", "fresh", "reach",
        "forall", "exists", "min", "max", "sum", "product", "num_of",
        "nothing", "everything", "not_specified",
        "typeof", "type", "elemtype", "lockset",
        "nonnullelements", "invariant_for", "is_initialized",
        "duration", "space", "working_space",
        "values", "index", "indices",
        "not_modified", "only_accessed", "only_assigned",
        "only_called", "only_captured",
        "exception", "witness", "empty", "singleton"
    );

    // -----------------------------------------------------------------------
    // Patterns
    // -----------------------------------------------------------------------

    private static final Pattern BACKSLASH_WORD = Pattern.compile("\\\\([a-zA-Z_][a-zA-Z0-9_]*)");
    private static final Pattern PLAIN_WORD     = Pattern.compile("[a-zA-Z_][a-zA-Z0-9_]*");

    // Detects the start of a JML line comment: optional whitespace then //@
    private static final Pattern JML_LINE_START = Pattern.compile("^(\\s*)//(@+)");
    // Detects the start of a JML block comment: optional whitespace then /*@
    private static final Pattern JML_BLOCK_START = Pattern.compile("^(\\s*)/\\*(@+)");

    // -----------------------------------------------------------------------
    // Public API
    // -----------------------------------------------------------------------

    /**
     * Compute semantic tokens for {@code source}.
     *
     * @param source the full Java source text
     * @return LSP-encoded semantic tokens (delta-encoded 5-integer tuples)
     */
    public static SemanticTokens computeTokens(String source) {
        List<Integer> data = new ArrayList<>();
        String[] lines = source.split("\n", -1);

        int prevLine = 0;
        int prevCol  = 0;
        boolean inBlockJml = false;

        for (int lineIdx = 0; lineIdx < lines.length; lineIdx++) {
            String line = lines[lineIdx];

            int jmlContentStart;     // column where JML content begins (after //@ or /*@)
            boolean isJmlLine;

            if (inBlockJml) {
                isJmlLine = true;
                // Skip leading whitespace + optional leading * (Javadoc style)
                int col = 0;
                while (col < line.length() && Character.isWhitespace(line.charAt(col))) col++;
                if (col < line.length() && line.charAt(col) == '*') col++;
                jmlContentStart = col;
                // Detect end of block comment
                if (line.contains("@*/") || line.contains("*/")) {
                    inBlockJml = false;
                }
            } else {
                Matcher lm = JML_LINE_START.matcher(line);
                Matcher bm = JML_BLOCK_START.matcher(line);
                if (lm.find()) {
                    isJmlLine = true;
                    jmlContentStart = lm.end();  // after //@
                } else if (bm.find()) {
                    isJmlLine = true;
                    jmlContentStart = bm.end();  // after /*@
                    if (!line.contains("*/")) inBlockJml = true;
                } else {
                    continue;
                }
            }

            if (!isJmlLine) continue;

            // Collect [col, length, tokenType] triples for this line.
            List<int[]> lineTokens = new ArrayList<>();
            String content = line.substring(Math.min(jmlContentStart, line.length()));
            int base = jmlContentStart;

            // 1. Backslash-expressions (e.g. \result, \old) → TT_MACRO
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

            // Sort by column so delta encoding is monotonically increasing.
            lineTokens.sort(Comparator.comparingInt(t -> t[0]));

            // Delta-encode and append to data.
            for (int[] tok : lineTokens) {
                int dLine = lineIdx - prevLine;
                int dCol  = (dLine == 0) ? tok[0] - prevCol : tok[0];
                data.add(dLine);
                data.add(dCol);
                data.add(tok[1]);   // length
                data.add(tok[2]);   // token type index
                data.add(0);        // token modifiers bitmask
                prevLine = lineIdx;
                prevCol  = tok[0];
            }
        }

        return new SemanticTokens(data);
    }
}
