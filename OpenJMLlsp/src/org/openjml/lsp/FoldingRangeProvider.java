package org.openjml.lsp;

import org.eclipse.lsp4j.FoldingRange;
import org.eclipse.lsp4j.FoldingRangeKind;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

/**
 * Computes LSP {@link FoldingRange}s for JML annotations in Java source.
 *
 * <p>A fold covers a maximal sequence of consecutive JML comment lines with no
 * non-JML lines interspersed.  A "JML line" is any line whose non-whitespace
 * content starts with a JML annotation marker:
 * <ul>
 *   <li>{@code //@} or {@code // @} — JML line comment</li>
 *   <li>{@code /*@} or {@code /* @} — start of a JML block comment;
 *       subsequent lines through the closing {@code *}{@code /} are included</li>
 * </ul>
 *
 * <p>Only ranges of two or more lines are emitted (single-line JML comments
 * do not need a fold handle).  The kind is set to {@link FoldingRangeKind#Comment}.
 * This is a pure text scan — no AST is required.
 */
public class FoldingRangeProvider {

    /**
     * Matches a JML line comment: optional whitespace, then {@code //} followed by
     * optional whitespace, then an optional sequence of conditional keys
     * ({@code [+-][a-zA-Z][a-zA-Z0-9_]*}), then {@code @}.
     * Examples: {@code //@}, {@code // @}, {@code //+ESC@}, {@code //-JML@}.
     */
    private static final Pattern JML_LINE_COMMENT =
            Pattern.compile("^[ \\t]*//[ \\t]*([+-][a-zA-Z][a-zA-Z0-9_]*)*@");

    /**
     * Matches the start of a JML block comment: optional whitespace, then {@code /*}
     * followed by optional whitespace, then an optional sequence of conditional keys,
     * then {@code @}.
     * Examples: {@code /*@}, {@code /* @}, {@code /*+ESC@}.
     */
    private static final Pattern JML_BLOCK_COMMENT_START =
            Pattern.compile("^[ \\t]*/\\*[ \\t]*([+-][a-zA-Z][a-zA-Z0-9_]*)*@");

    /**
     * Scan {@code source} and return folding ranges for JML annotation blocks.
     *
     * @param source full source text of the file
     * @return list of {@link FoldingRange}s (may be empty)
     */
    public static List<FoldingRange> fromSource(String source) {
        String[] lines = source.split("\\r?\\n", -1);
        List<FoldingRange> result = new ArrayList<>();

        int regionStart = -1;   // first line of current JML region (-1 = none)
        int regionEnd   = -1;   // last  line of current JML region
        boolean inBlock = false; // inside a multi-line JML block comment

        for (int i = 0; i < lines.length; i++) {
            String line = lines[i];

            if (inBlock) {
                // Still inside a JML block comment — extend the region.
                regionEnd = i;
                if (line.contains("*/")) {
                    inBlock = false;
                }
            } else if (JML_LINE_COMMENT.matcher(line).find()) {
                if (regionStart == -1) regionStart = i;
                regionEnd = i;
            } else if (JML_BLOCK_COMMENT_START.matcher(line).find()) {
                if (regionStart == -1) regionStart = i;
                regionEnd = i;
                if (!line.contains("*/")) {
                    inBlock = true;
                }
            } else {
                // Non-JML line — emit any pending region and reset.
                emitIfMultiLine(result, regionStart, regionEnd);
                regionStart = -1;
                regionEnd   = -1;
            }
        }

        // Emit any region that extends to the end of the file.
        emitIfMultiLine(result, regionStart, regionEnd);

        return result;
    }

    private static void emitIfMultiLine(List<FoldingRange> out, int start, int end) {
        if (start >= 0 && end > start) {
            FoldingRange fr = new FoldingRange(start, end);
            fr.setKind(FoldingRangeKind.Comment);
            out.add(fr);
        }
    }

    private FoldingRangeProvider() {}
}
