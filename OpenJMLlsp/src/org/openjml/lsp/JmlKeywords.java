package org.openjml.lsp;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Authoritative lists of JML and Java reserved words used throughout the LSP server.
 *
 * <p>There are four separate consumers, each with slightly different needs:
 * <ul>
 *   <li>{@link JmlCompletionProvider} — ordered lists for auto-complete items</li>
 *   <li>{@link SemanticTokensProvider} — sets for O(1) membership in regex fallback</li>
 *   <li>{@link Renamer} — set of Java keywords that are illegal as new identifiers</li>
 *   <li>{@code jml.tmLanguage.json} — TextMate grammar; kept in sync manually; see
 *       the comment at the bottom of that file for the canonical source reference.</li>
 * </ul>
 *
 * <p>All keyword lists are defined here and referenced by the classes above.  The
 * TextMate grammar cannot import from Java, so it must be updated manually whenever
 * this file changes — see {@code OpenJMLlsp/vscode-extension/syntaxes/jml.tmLanguage.json}
 * and {@code OpenJMLUI/syntaxes/jml.tmLanguage.json}.
 */
public final class JmlKeywords {

    private JmlKeywords() {}

    // -----------------------------------------------------------------------
    // JML keyword sets (authoritative — used for highlighting and validation)
    // -----------------------------------------------------------------------

    /**
     * Complete set of JML clause and modifier keywords (no backslash prefix).
     *
     * <p>Used by {@link SemanticTokensProvider} for the regex fallback highlight
     * pass.  A superset of {@link #JML_KEYWORD_COMPLETIONS}.
     */
    public static final Set<String> JML_KEYWORDS = Set.of(
        // specification method clauses
        "requires", "old", "ensures", "signals", "signals_only", "assignable",
        "modifies", "accessible", "callable", "measured_by", "captures",
        "diverges", "when", "working_space", "duration",
        "breaks", "continues", "returns",
        // type-member clauses
        "invariant", "initially", "constraint", "represents", "axiom",
        "readable", "writable", "monitors_for",
        // case combinators
        "also", "implies_that", "for_example", "example",
        // behavior keywords
        "behavior", "normal_behavior", "exceptional_behavior",
        // declaration modifiers
        "pure", "spec_pure", "strictly_pure", "no_state", "two_state",
         "ghost", "model",
        "spec_public", "spec_protected", 
        "non_null", "non_null_by_default", "nullable", "nullable_by_default",
        "helper", "instance", "query", "secret",
        "monitored", "uninitialized",
        "code_java_math", "code_safe_math", "code_bigint_math",
        "spec_java_math", "spec_safe_math", "spec_bigint_math",
        // statement / expression keywords
        "loop_invariant", "maintaining", "decreasing", "decreases",
        "assume", "assert", "set", "debug", "hence_by", "unreachable",
        "reachable", "in", "maps"
    );

    /**
     * Complete set of JML backslash-expression names (the part AFTER the {@code \}).
     *
     * <p>Used by {@link SemanticTokensProvider} for the regex fallback highlight
     * pass.  A superset of the names in {@link #JML_BACKSLASH_COMPLETIONS}.
     */
    public static final Set<String> JML_BACKSLASH = Set.of(
        // common value expressions
        "result", "old", "pre", "past", "fresh", "reach",
        // quantifiers
        "forall", "exists", "min", "max", "sum", "product", "num_of",
        // store-ref keywords
        "nothing", "everything", "not_specified", "strictly_nothing",
        // type expressions
        "typeof", "type", "elemtype", "bigint", "real", "set", "map", "string", "array", "seq", "datagroup", "locset",
        // heap/object checks
        "lockset", "nonnullelements", "nonnullelementsx", "invariant_for", "is_initialized",
        // frame conditions / bounds
        "not_assigned", "not_modified",
        "only_accessed", "only_assigned", "only_called", "only_captured",
        // labels
        "lbl", "lblneg", "lblpos",
        // time/space (rarely used)
        "duration", "space", "working_space",
        // loop / sequence
        "values", "count", "index", 
        // misc
        "exception", "witness", "empty", "singleton", "same"
    );

    // -----------------------------------------------------------------------
    // Ordered completion lists (used by JmlCompletionProvider)
    // -----------------------------------------------------------------------

    /**
     * Ordered list of JML clause and modifier keywords offered as completion items.
     *
     * <p>Derived from {@link #JML_KEYWORDS}: every entry sorted alphabetically.
     * Adding or removing from {@code JML_KEYWORDS} automatically updates this list.
     */
    public static final List<String> JML_KEYWORD_COMPLETIONS =
            JML_KEYWORDS.stream()
                        .sorted()
                        .collect(Collectors.toUnmodifiableList());

    /**
     * Ordered list of JML backslash-prefixed tokens offered as completion items
     * (each entry includes the leading {@code \}).
     *
     * <p>Derived from {@link #JML_BACKSLASH}: every entry sorted alphabetically
     * with a {@code \} prepended.  Adding or removing from {@code JML_BACKSLASH}
     * automatically updates this list.
     */
    public static final List<String> JML_BACKSLASH_COMPLETIONS =
            JML_BACKSLASH.stream()
                         .sorted()
                         .map(s -> "\\" + s)
                         .collect(Collectors.toUnmodifiableList());

    // -----------------------------------------------------------------------
    // Java reserved words
    // -----------------------------------------------------------------------

    /**
     * Java reserved keywords and literals that are illegal as identifiers.
     *
     * <p>Used by {@link Renamer} to reject rename targets that would produce
     * illegal identifiers.
     */
    public static final Set<String> JAVA_KEYWORDS = Set.of(
        "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char",
        "class", "const", "continue", "default", "do", "double", "else", "enum",
        "extends", "final", "finally", "float", "for", "goto", "if", "implements",
        "import", "instanceof", "int", "interface", "long", "native", "new",
        "package", "private", "protected", "public", "return", "short", "static",
        "strictfp", "super", "switch", "synchronized", "this", "throw", "throws",
        "transient", "try", "void", "volatile", "while",
        // boolean/null literals are not keywords but also forbidden as identifiers
        "true", "false", "null"
    );

    /**
     * Java access and modifier keywords that may appear in JML ghost/model declarations.
     *
     * <p>Used by {@link SemanticTokensProvider} to highlight modifier words that
     * appear between the start of a JML ghost/model declaration and its type.
     */
    public static final Set<String> JAVA_MODIFIERS = Set.of(
        "public", "protected", "private", "static", "abstract", "final",
        "synchronized", "native", "strictfp", "transient", "volatile"
    );
}
