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
 * <p>A JML folding range starts on a line that <em>ends with</em> a JML comment:
 * <ul>
 *   <li>a JML line comment ({@code //@}, {@code // @}, {@code //+KEY@}, etc.), or</li>
 *   <li>an unterminated JML block comment ({@code /*@} without a closing
 *       {@code *}{@code /} on the same line), or</li>
 *   <li>a terminated JML block comment ({@code /*@ ... *}{@code /}) followed only
 *       by whitespace and/or Java comments.</li>
 * </ul>
 *
 * <p>The range continues forward as long as each successive line contains only
 * JML comments, Java comments (line or block), or whitespace.  Two conditions
 * terminate the range:
 * <ul>
 *   <li>A blank line (only whitespace) that is <em>not</em> inside an ongoing
 *       multi-line block comment (JML or Java).</li>
 *   <li>A line with non-whitespace, non-comment program text.</li>
 * </ul>
 * Blank lines that fall inside a multi-line block comment are part of that
 * comment and do <em>not</em> terminate the range.
 *
 * <p>Java-only comments (no JML) do <em>not</em> start a folding range; they
 * can only extend one that has already started.
 *
 * <p>Only ranges spanning two or more lines are emitted; single-line JML
 * comments need no fold handle.  The kind is set to
 * {@link FoldingRangeKind#Comment}.  This is a pure text scan -- no AST is
 * required.
 */
public class FoldingRangeProvider {

    /**
     * JML line-comment marker: {@code //} followed by optional whitespace,
     * optional conditional keys ({@code [+-]identifier}), then {@code @}.
     * Applied to the leading-whitespace-stripped line.
     * Examples: {@code //@}, {@code // @}, {@code //+ESC@}, {@code //-JML@}.
     */
    private static final Pattern JML_LINE =
            Pattern.compile("^//[ \\t]*([+-][a-zA-Z][a-zA-Z0-9_]*)*@");

    /**
     * JML block-comment start marker: {@code /*} followed by optional
     * whitespace, optional conditional keys, then {@code @}.
     * Applied to the leading-whitespace-stripped line.
     * Examples: {@code /*@}, {@code /* @}, {@code /*+ESC@}.
     */
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
        String[] lines = source.split("\\r?\\n", -1);
        List<FoldingRange> result = new ArrayList<>();

        int regionStart = -1;    // first line of active JML fold (-1 = none)
        int regionEnd   = -1;    // last  line included in the active fold
        boolean inBlock = false; // inside a multi-line block comment (JML or Java)

        for (int i = 0; i < lines.length; i++) {
            String line = lines[i];

            if (inBlock) {
                // -------------------------------------------------------
                // Interior of an ongoing multi-line block comment.
                // Any line here (even blank) extends the active region.
                // When "*/" is found, check trailing content.
                // -------------------------------------------------------
                int closePos = line.indexOf("*/");
                if (closePos < 0) {
                    // Block not yet closed -- extend region.
                    if (regionStart != -1) regionEnd = i;
                } else {
                    // Block closes on this line.
                    inBlock = false;
                    String tail = line.substring(closePos + 2);
                    if (hasProgramText(tail)) {
                        // Program text follows "*/" -- terminate region
                        // without including this line.
                        emitIfMultiLine(result, regionStart, regionEnd);
                        regionStart = -1;
                        regionEnd   = -1;
                    } else {
                        // Tail is whitespace/comments only -- include line.
                        if (regionStart != -1) regionEnd = i;
                    }
                }
                continue;
            }

            // ---------------------------------------------------------------
            // Not inside a block comment -- classify the line.
            // ---------------------------------------------------------------
            String trimmed = line.stripLeading();

            if (trimmed.isEmpty()) {
                // Blank line outside a block comment: terminates active region.
                emitIfMultiLine(result, regionStart, regionEnd);
                regionStart = -1;
                regionEnd   = -1;

            } else if (JML_LINE.matcher(trimmed).lookingAt()) {
                // JML line comment -- starts or extends a region.
                if (regionStart == -1) regionStart = i;
                regionEnd = i;

            } else if (JML_BLOCK.matcher(trimmed).lookingAt()) {
                // JML block comment -- starts or extends a region.
                if (regionStart == -1) regionStart = i;
                regionEnd = i;
                int closePos = line.indexOf("*/");
                if (closePos < 0) {
                    // Block continues onto subsequent lines.
                    inBlock = true;
                } else {
                    // Terminated on this line: check trailing content.
                    String tail = line.substring(closePos + 2);
                    if (hasProgramText(tail)) {
                        // Program text follows -- terminate immediately.
                        emitIfMultiLine(result, regionStart, regionEnd);
                        regionStart = -1;
                        regionEnd   = -1;
                    }
                    // else region continues normally
                }

            } else if (trimmed.startsWith("//")) {
                // Java line comment -- extends an active region; does NOT start one.
                if (regionStart != -1) regionEnd = i;

            } else if (trimmed.startsWith("/*")) {
                // Java block comment -- extends an active region; does NOT start one.
                if (regionStart != -1) {
                    int closePos = line.indexOf("*/");
                    if (closePos < 0) {
                        // Block continues onto subsequent lines.
                        regionEnd = i;
                        inBlock = true;
                    } else {
                        // Terminated on this line: check trailing content.
                        String tail = line.substring(closePos + 2);
                        if (hasProgramText(tail)) {
                            // Program text after close -- terminate without including line.
                            emitIfMultiLine(result, regionStart, regionEnd);
                            regionStart = -1;
                            regionEnd   = -1;
                        } else {
                            regionEnd = i;
                        }
                    }
                } else {
                    // No active region: still track the block so that interior
                    // lines (which might look like JML) are not misclassified.
                    if (!line.contains("*/")) {
                        inBlock = true;
                    }
                }

            } else {
                // Non-comment program text -- terminates active region.
                emitIfMultiLine(result, regionStart, regionEnd);
                regionStart = -1;
                regionEnd   = -1;
            }
        }

        // Emit any region that reaches the end of the file.
        emitIfMultiLine(result, regionStart, regionEnd);
        return result;
    }

    // -------------------------------------------------------------------
    // Helpers
    // -------------------------------------------------------------------

    /**
     * Returns {@code true} if {@code s} contains non-whitespace, non-comment
     * content (i.e., program text).  Handles arbitrarily many leading Java
     * line or block comments before deciding.
     */
    private static boolean hasProgramText(String s) {
        while (true) {
            s = s.stripLeading();
            if (s.isEmpty())         return false;
            if (s.startsWith("//")) return false;  // line comment consumes rest
            if (s.startsWith("/*")) {
                int close = s.indexOf("*/", 2);
                if (close < 0) return false;        // unclosed block -- treat as comment
                s = s.substring(close + 2);         // skip block, keep scanning
            } else {
                return true;                        // non-whitespace non-comment
            }
        }
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
