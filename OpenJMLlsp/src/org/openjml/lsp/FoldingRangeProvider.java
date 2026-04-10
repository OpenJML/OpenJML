package org.openjml.lsp;

import org.eclipse.lsp4j.FoldingRange;
import org.eclipse.lsp4j.FoldingRangeKind;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

/**
 * Computes LSP {@link FoldingRange}s for JML annotation blocks in Java source.
 *
 * <h3>Algorithm</h3>
 *
 * <ol>
 *   <li>Scan character by character to find the next JML comment start —
 *       a JML line comment ({@code //@}, {@code // @}, {@code //+KEY@}, etc.)
 *       or a JML block comment ({@code /*@}, {@code /* @}, {@code /*+KEY@},
 *       etc.) anywhere on a line.  Non-JML Java comments are skipped.</li>
 *   <li>Record {@code startLine}.  Consume the initial JML comment.  For a
 *       block comment followed by program text on the same line (after
 *       {@code *}{@code /}), skip to end of line and begin extending from the
 *       next line.</li>
 *   <li>Skip horizontal whitespace.  If the next character is a newline,
 *       consume it, skip leading whitespace on the new line, and stop if that
 *       line is blank.</li>
 *   <li>While the next two characters start a comment ({@code //} or
 *       {@code /*}): consume it.  For a block comment followed by program text
 *       on the same line, stop and rewind to just before the {@code /*} so
 *       the outer scan can treat it as a new fold start.  Then go to step 3.</li>
 *   <li>Emit a {@link FoldingRangeKind#Comment} range when
 *       {@code endLine > startLine}; continue outer scan.</li>
 * </ol>
 *
 * <p>This is a pure text scan — no AST is required.
 */
public class FoldingRangeProvider {

    /** JML line-comment marker: {@code //} + optional spaces/keys + {@code @}. */
    private static final Pattern JML_LINE =
            Pattern.compile("^//[ \\t]*([+-][a-zA-Z][a-zA-Z0-9_]*)*@");

    /** JML block-comment start marker: {@code /*} + optional spaces/keys + {@code @}. */
    private static final Pattern JML_BLOCK =
            Pattern.compile("^/\\*[ \\t]*([+-][a-zA-Z][a-zA-Z0-9_]*)*@");

    // -------------------------------------------------------------------
    // Public API
    // -------------------------------------------------------------------

    /**
     * Scan {@code source} and return folding ranges for JML annotation blocks.
     *
     * @param source full source text of the file
     * @return list of {@link FoldingRange}s, may be empty
     */
    public static List<FoldingRange> fromSource(String source) {
        List<FoldingRange> result = new ArrayList<>();
        int n   = source.length();
        int pos = 0;
        int line = 0;

        while (pos < n) {
            // ---- Phase 1: find the next JML comment start ----
            int[] jmlStart = findJmlCommentStart(source, n, pos, line);
            if (jmlStart == null) break;

            pos  = jmlStart[0];
            line = jmlStart[1];
            boolean isLineComment = (jmlStart[2] == 0);
            int startLine = line;
            int endLine   = startLine;

            // ---- Consume the initial JML comment ----
            if (isLineComment) {
                pos = skipToNewline(source, n, pos); // pos at \n or EOF
            } else {
                int[] after = skipBlockComment(source, n, pos, line);
                pos  = after[0];
                line = after[1];
                endLine = line;
                if (hasProgramText(source, n, pos)) {
                    // Program text after */: skip rest of line; extend from next line.
                    pos = skipToNewline(source, n, pos);
                }
            }

            // ---- Extension loop ----
            while (true) {
                // Skip trailing spaces/tabs on current line.
                while (pos < n && isSpaceOrTab(source.charAt(pos))) pos++;

                if (pos >= n) break;

                char c = source.charAt(pos);

                if (c == '\n' || c == '\r') {
                    // Consume newline and advance to the next line.
                    if (c == '\r' && pos + 1 < n && source.charAt(pos + 1) == '\n') pos++;
                    pos++; line++;

                    // Skip leading spaces/tabs on the new line.
                    while (pos < n && isSpaceOrTab(source.charAt(pos))) pos++;

                    if (pos >= n) break; // EOF
                    c = source.charAt(pos);
                    if (c == '\n' || c == '\r') break; // blank line: stop

                    // Fall through: c is the first non-space-tab char of the new line.
                }

                // Is c the start of a comment?
                if (c == '/' && pos + 1 < n) {
                    char c2 = source.charAt(pos + 1);
                    if (c2 == '/') {
                        // Any line comment extends the fold.
                        endLine = line;
                        pos = skipToNewline(source, n, pos);
                        continue;
                    }
                    if (c2 == '*') {
                        int savePos  = pos;
                        int saveLine = line;
                        int[] after = skipBlockComment(source, n, pos, line);
                        int posAfter  = after[0];
                        int lineAfter = after[1];
                        if (hasProgramText(source, n, posAfter)) {
                            // Program text after */: stop and rewind so outer scan
                            // treats this /* as a new fold start.
                            // emitIfMultiLine is called after the loop with endLine.
                            pos  = savePos;
                            line = saveLine;
                            break;
                        }
                        endLine = lineAfter;
                        pos  = posAfter;
                        line = lineAfter;
                        continue;
                    }
                }

                // Not a comment: terminate fold.
                break;
            }

            emitIfMultiLine(result, startLine, endLine);
            // Outer loop continues from current pos/line.
        }

        return result;
    }

    // -------------------------------------------------------------------
    // Helpers
    // -------------------------------------------------------------------

    /**
     * Scans forward from {@code pos} to find the next JML comment start.
     * Non-JML Java {@code //} and {@code /*} comments are skipped entirely.
     *
     * @return {@code [pos, line, type]} — type 0 = line comment, 1 = block
     *         comment — or {@code null} if none remains.
     */
    private static int[] findJmlCommentStart(String source, int n, int pos, int line) {
        while (pos < n) {
            char c = source.charAt(pos);
            if (c == '\n') { pos++; line++; continue; }
            if (c == '\r') {
                pos++;
                if (pos < n && source.charAt(pos) == '\n') pos++;
                line++;
                continue;
            }
            if (c == '/' && pos + 1 < n) {
                char c2 = source.charAt(pos + 1);
                if (c2 == '/') {
                    if (isJmlLineStart(source, n, pos)) return new int[]{pos, line, 0};
                    pos = skipToNewline(source, n, pos); // skip regular // comment
                    continue;
                }
                if (c2 == '*') {
                    if (isJmlBlockStart(source, n, pos)) return new int[]{pos, line, 1};
                    int[] after = skipBlockComment(source, n, pos, line); // skip regular /* comment
                    pos = after[0]; line = after[1];
                    continue;
                }
            }
            pos++;
        }
        return null;
    }

    /** Returns true if {@code //} at {@code pos} starts a JML line comment. */
    private static boolean isJmlLineStart(String source, int n, int pos) {
        return JML_LINE.matcher(source).region(pos, n).lookingAt();
    }

    /** Returns true if {@code /*} at {@code pos} starts a JML block comment. */
    private static boolean isJmlBlockStart(String source, int n, int pos) {
        return JML_BLOCK.matcher(source).region(pos, n).lookingAt();
    }

    /**
     * Advances to just before the next newline (or EOF), without consuming it.
     */
    private static int skipToNewline(String source, int n, int pos) {
        while (pos < n && source.charAt(pos) != '\n' && source.charAt(pos) != '\r') pos++;
        return pos;
    }

    /**
     * Skips a block comment starting at {@code pos} (which must be at
     * {@code /*}).  Handles unclosed comments by returning EOF.
     *
     * @return {@code [newPos, newLine]} — {@code newPos} just after
     *         {@code *}{@code /}, or {@code n} if unclosed.
     */
    private static int[] skipBlockComment(String source, int n, int pos, int line) {
        pos += 2; // skip /*
        while (pos < n) {
            char c = source.charAt(pos);
            if (c == '\n') { pos++; line++; continue; }
            if (c == '\r') { pos++; if (pos < n && source.charAt(pos) == '\n') pos++; line++; continue; }
            if (c == '*' && pos + 1 < n && source.charAt(pos + 1) == '/') {
                return new int[]{pos + 2, line};
            }
            pos++;
        }
        return new int[]{n, line}; // unclosed
    }

    /**
     * Returns {@code true} if the text from {@code pos} to end of line
     * contains non-whitespace, non-comment content (program text).
     */
    private static boolean hasProgramText(String source, int n, int pos) {
        while (pos < n) {
            char c = source.charAt(pos);
            if (c == '\n' || c == '\r') return false;
            if (c == ' ' || c == '\t') { pos++; continue; }
            if (c == '/' && pos + 1 < n) {
                char c2 = source.charAt(pos + 1);
                if (c2 == '/') return false; // line comment: rest of line is comment
                if (c2 == '*') {
                    int[] after = skipBlockComment(source, n, pos, 0);
                    pos = after[0];
                    continue;
                }
            }
            return true; // non-whitespace, non-comment
        }
        return false; // EOF
    }

    private static boolean isSpaceOrTab(char c) { return c == ' ' || c == '\t'; }

    private static void emitIfMultiLine(List<FoldingRange> out, int start, int end) {
        if (start >= 0 && end > start) {
            FoldingRange fr = new FoldingRange(start, end);
            fr.setKind(FoldingRangeKind.Comment);
            out.add(fr);
        }
    }

    private FoldingRangeProvider() {}
}
