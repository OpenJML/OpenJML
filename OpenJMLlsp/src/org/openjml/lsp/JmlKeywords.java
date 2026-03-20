package org.openjml.lsp;

import java.util.List;
import java.util.Set;

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
        "requires", "ensures", "signals", "signals_only", "assignable",
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
        "pure", "ghost", "model",
        "spec_public", "spec_protected", "spec_private",
        "non_null", "non_null_by_default", "nullable", "nullable_by_default",
        "helper", "instance", "query", "secret",
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
     * Complete set of JML backslash-expression names (the part AFTER the {@code \}).
     *
     * <p>Used by {@link SemanticTokensProvider} for the regex fallback highlight
     * pass.  A superset of the names in {@link #JML_BACKSLASH_COMPLETIONS}.
     */
    public static final Set<String> JML_BACKSLASH = Set.of(
        // common value expressions
        "result", "old", "pre", "fresh", "reach",
        // quantifiers
        "forall", "exists", "min", "max", "sum", "product", "num_of",
        // store-ref keywords
        "nothing", "everything", "not_specified", "strictly_nothing",
        // type expressions
        "typeof", "type", "elemtype", "bigint", "real",
        // heap/object checks
        "lockset", "nonnullelements", "invariant_for", "is_initialized",
        // frame conditions / bounds
        "not_assigned", "not_modified",
        "only_accessed", "only_assigned", "only_called", "only_captured",
        // labels
        "lblneg", "lblpos",
        // time/space (rarely used)
        "duration", "space", "working_space",
        // loop / sequence
        "values", "index", "indices",
        // misc
        "exception", "witness", "empty", "singleton", "same"
    );

    // -----------------------------------------------------------------------
    // Ordered completion lists (used by JmlCompletionProvider)
    // -----------------------------------------------------------------------

    /**
     * Ordered list of JML clause and modifier keywords offered as completion items.
     *
     * <p>This is a curated subset of {@link #JML_KEYWORDS} containing the keywords
     * most commonly needed at the top level of a JML annotation.
     */
    public static final List<String> JML_KEYWORD_COMPLETIONS = List.of(
        // Specification cases
        "also", "behavior", "exceptional_behavior", "normal_behavior",
        // Clauses
        "accessible", "assignable", "axiom", "captures", "constraint",
        "decreases", "ensures", "hence_by", "initially", "invariant",
        "loop_invariant", "maintaining", "modifies", "requires",
        "signals", "signals_only",
        // Statement annotations
        "assert", "assume", "unreachable",
        // Modifiers
        "ghost", "helper", "instance", "model", "non_null",
        "non_null_by_default", "nullable", "nullable_by_default",
        "pure", "spec_bigint_math", "spec_java_math", "spec_protected",
        "spec_public", "spec_safe_math"
    );

    /**
     * Ordered list of JML backslash-prefixed tokens offered as completion items
     * (each entry includes the leading {@code \}).
     *
     * <p>This is a curated subset of the names in {@link #JML_BACKSLASH}.
     */
    public static final List<String> JML_BACKSLASH_COMPLETIONS = List.of(
        "\\bigint", "\\elemtype", "\\everything", "\\exists",
        "\\forall", "\\fresh", "\\invariant_for", "\\is_initialized",
        "\\lblneg", "\\lblpos", "\\lockset",
        "\\max", "\\min", "\\not_assigned", "\\not_modified",
        "\\not_specified", "\\nothing", "\\nonnullelements",
        "\\num_of", "\\old", "\\only_accessed", "\\only_assigned",
        "\\only_called", "\\only_captured", "\\pre", "\\product",
        "\\reach", "\\real", "\\result", "\\same",
        "\\strictly_nothing", "\\sum", "\\type", "\\typeof"
    );

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
