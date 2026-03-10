package org.openjml.lsp;

import org.eclipse.lsp4j.CompletionItem;
import org.eclipse.lsp4j.CompletionItemKind;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.TextEdit;
import org.eclipse.lsp4j.jsonrpc.messages.Either;

import java.util.ArrayList;
import java.util.List;

/**
 * Provides static-list JML completion items for use inside JML annotations
 * ({@code //@ ...} and {@code /*@ ... *}{@code /}).
 *
 * <p>Two categories are offered:
 * <ul>
 *   <li><b>Keywords</b> — JML clause and modifier names ({@code requires},
 *       {@code ensures}, {@code ghost}, etc.) offered when the cursor is
 *       inside a JML annotation and the partial word does not start with
 *       {@code \}.</li>
 *   <li><b>Backslash tokens</b> — JML built-in expressions ({@code \result},
 *       {@code \old}, {@code \forall}, etc.) offered when the partial word
 *       starts with {@code \}.</li>
 * </ul>
 *
 * <p>JML context detection recognises:
 * <ul>
 *   <li>Single-line annotations: {@code //@} (optional spaces between {@code //}
 *       and {@code @}) anywhere before the cursor on the current line.</li>
 *   <li>Block annotations: an unclosed {@code /*@} (optional spaces between
 *       {@code /*} and {@code @}) in the text before the cursor.</li>
 * </ul>
 */
public class JmlCompletionProvider {

    // -----------------------------------------------------------------------
    // Static keyword list
    // -----------------------------------------------------------------------

    /** JML clause and modifier keywords, alphabetically ordered. */
    private static final String[] KEYWORDS = {
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
        "spec_public", "spec_safe_math",
    };

    // -----------------------------------------------------------------------
    // Static backslash-token list
    // -----------------------------------------------------------------------

    /** JML {@code \}-prefixed built-in expressions and types. */
    private static final String[] BACKSLASH_TOKENS = {
        // Common expression tokens
        "\\bigint", "\\elemtype", "\\everything", "\\exists",
        "\\forall", "\\fresh", "\\invariant_for", "\\is_initialized",
        "\\lblneg", "\\lblpos", "\\lockset",
        "\\max", "\\min", "\\not_assigned", "\\not_modified",
        "\\not_specified", "\\nothing", "\\nonnullelements",
        "\\num_of", "\\old", "\\only_accessed", "\\only_assigned",
        "\\only_called", "\\only_captured", "\\pre", "\\product",
        "\\reach", "\\real", "\\result", "\\same",
        "\\strictly_nothing", "\\sum", "\\type", "\\typeof",
    };

    // -----------------------------------------------------------------------
    // Pre-built completion item lists (built once at class-load time)
    // -----------------------------------------------------------------------

    private static final List<CompletionItem> ALL_KEYWORD_ITEMS;
    private static final List<CompletionItem> ALL_BACKSLASH_ITEMS;

    static {
        ALL_KEYWORD_ITEMS = new ArrayList<>(KEYWORDS.length);
        for (String kw : KEYWORDS) {
            CompletionItem item = new CompletionItem(kw);
            item.setKind(CompletionItemKind.Keyword);
            ALL_KEYWORD_ITEMS.add(item);
        }

        ALL_BACKSLASH_ITEMS = new ArrayList<>(BACKSLASH_TOKENS.length);
        for (String tok : BACKSLASH_TOKENS) {
            CompletionItem item = new CompletionItem(tok);
            item.setKind(CompletionItemKind.Keyword);
            ALL_BACKSLASH_ITEMS.add(item);
        }
    }

    // -----------------------------------------------------------------------
    // Public API
    // -----------------------------------------------------------------------

    /**
     * Return completion items appropriate for the cursor position in
     * {@code content}, or an empty list if the cursor is not inside a JML
     * annotation.
     *
     * @param content full document text
     * @param pos     0-based LSP cursor position
     */
    public static List<CompletionItem> complete(String content, Position pos) {
        if (!isInJmlContext(content, pos)) return List.of();
        String prefix = wordBeforeCursor(content, pos);
        if (prefix.startsWith("\\")) {
            // VS Code does not treat '\' as a word character, so without a TextEdit
            // it would insert the completion after the '\', producing '\\result'.
            // Supply an explicit replace-range covering from the '\' to the cursor.
            Range replaceRange = wordBeforeCursorRange(content, pos);
            List<CompletionItem> items = new ArrayList<>(ALL_BACKSLASH_ITEMS.size());
            for (CompletionItem tmpl : ALL_BACKSLASH_ITEMS) {
                CompletionItem item = new CompletionItem(tmpl.getLabel());
                item.setKind(tmpl.getKind());
                item.setTextEdit(Either.forLeft(new TextEdit(replaceRange, tmpl.getLabel())));
                items.add(item);
            }
            return items;
        }
        return ALL_KEYWORD_ITEMS;
    }

    // -----------------------------------------------------------------------
    // Context detection
    // -----------------------------------------------------------------------

    /**
     * Returns {@code true} when the cursor is inside a JML annotation.
     *
     * <p>Recognises {@code //@} (single-line) and {@code /*@} (block) with
     * optional whitespace between the comment opener and the {@code @}.
     */
    static boolean isInJmlContext(String content, Position pos) {
        String[] lines = content.split("\n", -1);
        if (pos.getLine() >= lines.length) return false;
        String line = lines[pos.getLine()];
        int col = Math.min(pos.getCharacter(), line.length());
        String linePrefix = line.substring(0, col);

        // Single-line: //  optionalSpaces  @  before cursor on this line
        if (java.util.regex.Pattern.compile("//\\s*@").matcher(linePrefix).find()) return true;

        // Block comment: /*  optionalSpaces  @  opened before cursor, not yet closed
        int offset = positionToOffset(content, pos);
        // Search backwards for the most recent /*@ opener
        int searchFrom = Math.max(0, offset - 1);
        String beforeCursor = content.substring(0, searchFrom + 1);
        // Find last occurrence of /*  (optional spaces)  @
        java.util.regex.Matcher opener = java.util.regex.Pattern
                .compile("/\\*\\s*@")
                .matcher(beforeCursor);
        int lastOpen = -1;
        while (opener.find()) lastOpen = opener.start();
        if (lastOpen < 0) return false;
        // Check that the block comment is not yet closed before the cursor
        int closePos = content.indexOf("*/", lastOpen + 2);
        return closePos < 0 || closePos >= offset;
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /**
     * Return the partial word (including a leading {@code \} if present)
     * immediately before the cursor.
     */
    static String wordBeforeCursor(String content, Position pos) {
        String[] lines = content.split("\n", -1);
        if (pos.getLine() >= lines.length) return "";
        String line = lines[pos.getLine()];
        int col = Math.min(pos.getCharacter(), line.length());
        int i = col - 1;
        while (i >= 0) {
            char c = line.charAt(i);
            if (c == '\\' || Character.isLetterOrDigit(c) || c == '_') i--;
            else break;
        }
        return line.substring(i + 1, col);
    }

    /**
     * Return the LSP {@link Range} that covers the partial word (including a
     * leading {@code \}) immediately before the cursor — i.e. the range a
     * TextEdit should replace.
     */
    static Range wordBeforeCursorRange(String content, Position pos) {
        String[] lines = content.split("\n", -1);
        if (pos.getLine() >= lines.length) return new Range(pos, pos);
        String line = lines[pos.getLine()];
        int col = Math.min(pos.getCharacter(), line.length());
        int i = col - 1;
        while (i >= 0) {
            char c = line.charAt(i);
            if (c == '\\' || Character.isLetterOrDigit(c) || c == '_') i--;
            else break;
        }
        Position start = new Position(pos.getLine(), i + 1);
        Position end   = new Position(pos.getLine(), col);
        return new Range(start, end);
    }

    /** Convert a 0-based LSP {@link Position} to a character offset in {@code content}. */
    private static int positionToOffset(String content, Position pos) {
        int line = 0, col = 0, offset = 0;
        while (offset < content.length()) {
            if (line == pos.getLine() && col == pos.getCharacter()) break;
            char c = content.charAt(offset++);
            if (c == '\n') { line++; col = 0; } else col++;
        }
        return offset;
    }

    private JmlCompletionProvider() {}
}
