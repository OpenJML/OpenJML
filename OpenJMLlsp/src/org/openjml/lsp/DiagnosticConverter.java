package org.openjml.lsp;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;

import javax.tools.JavaFileObject;
import java.util.Locale;

/**
 * Converts a {@code javax.tools.Diagnostic} to an LSP {@code Diagnostic}.
 *
 * <p>Position conventions:
 * <ul>
 *   <li>javax.tools.Diagnostic: 1-indexed line; {@code NOPOS} (-1) means unknown</li>
 *   <li>LSP: 0-indexed lines and characters</li>
 * </ul>
 *
 * <p>javac's {@code getColumnNumber()} expands tabs to 8-space visual stops, which
 * disagrees with LSP's character definition (tab = 1 code unit).  To avoid this, the
 * primary column computation uses {@code JCDiagnostic.getDiagnosticSource().getColumnNumber(pos, false)},
 * which returns the raw character offset (no tab expansion).  When that is not available
 * the fallback is a precomputed {@code lineStartOffsets} array, or finally
 * {@code getColumnNumber()-1} (which may be wrong for tab-indented code).
 */
public class DiagnosticConverter {

    /**
     * Builds a line-start-offset table from a source string.
     * {@code result[i]} is the character offset of the first character of line {@code i}
     * (0-indexed).  The table can be passed to {@link #convert} to avoid tab-expansion
     * errors in javac's column numbers.
     */
    public static int[] buildLineStartOffsets(String content) {
        // Count lines first so we can allocate exactly.
        int lines = 1;
        for (int i = 0; i < content.length(); i++) {
            char c = content.charAt(i);
            if (c == '\n') lines++;
            else if (c == '\r') {
                lines++;
                if (i + 1 < content.length() && content.charAt(i + 1) == '\n') i++;
            }
        }
        int[] offsets = new int[lines];
        int line = 0;
        for (int i = 0; i < content.length(); i++) {
            char c = content.charAt(i);
            if (c == '\r') {
                if (i + 1 < content.length() && content.charAt(i + 1) == '\n') i++;
                offsets[++line] = i + 1;
            } else if (c == '\n') {
                offsets[++line] = i + 1;
            }
        }
        return offsets;
    }

    /** Convert without a line-start table. */
    public static Diagnostic convert(
            javax.tools.Diagnostic<? extends JavaFileObject> d,
            String sourcePath,
            String targetUri) {
        return convert(d, sourcePath, targetUri, null);
    }

    public static Diagnostic convert(
            javax.tools.Diagnostic<? extends JavaFileObject> d,
            String sourcePath,
            String targetUri,
            int[] lineStartOffsets) {

        // Skip diagnostics from files other than the one being checked.
        if (d.getSource() != null && sourcePath != null) {
            String srcName = d.getSource().getName();
            if (!srcName.isEmpty() && !srcName.endsWith(baseName(sourcePath))) {
                return null;
            }
        }

        long line = d.getLineNumber();
        int lspLine = line > 0 ? (int)(line - 1) : 0;

        long startPos = d.getStartPosition();
        long endPos   = d.getEndPosition();

        // Compute LSP character offset (tab = 1 code unit, no expansion).
        //
        // Primary: JCDiagnostic.getDiagnosticSource().getColumnNumber(pos, false)
        //   — javac's own column lookup with expandTabs=false; 1-indexed → subtract 1.
        // Secondary: precomputed lineStartOffsets array (startPos - lineStartOffsets[line]).
        // Fallback: javac's getColumnNumber()-1 (may be wrong for tabs).
        int lspCol = -1;

        if (startPos != javax.tools.Diagnostic.NOPOS
                && d instanceof com.sun.tools.javac.util.JCDiagnostic jcd) {
            var src = jcd.getDiagnosticSource();
            if (src != null) {
                try {
                    int raw = src.getColumnNumber((int) startPos, false);
                    if (raw > 0) lspCol = raw - 1;  // 1-indexed → 0-indexed
                } catch (Exception ignored) {}
            }
        }

        if (lspCol < 0) {
            if (lineStartOffsets != null
                    && startPos != javax.tools.Diagnostic.NOPOS
                    && lspLine < lineStartOffsets.length) {
                lspCol = Math.max((int)(startPos - lineStartOffsets[lspLine]), 0);
            } else {
                long col = d.getColumnNumber();
                lspCol = col > 0 ? (int)(col - 1) : 0;
            }
        }

        Range range;
        if (startPos != javax.tools.Diagnostic.NOPOS
                && endPos   != javax.tools.Diagnostic.NOPOS
                && endPos   >= startPos) {
            int endCol = (int)(lspCol + (endPos - startPos));
            range = new Range(new Position(lspLine, lspCol),
                              new Position(lspLine, endCol));
        } else {
            var pt = new Position(lspLine, lspCol);
            range = new Range(pt, pt);
        }

        DiagnosticSeverity severity = switch (d.getKind()) {
            case ERROR            -> DiagnosticSeverity.Error;
            case WARNING,
                 MANDATORY_WARNING -> DiagnosticSeverity.Warning;
            case NOTE             -> DiagnosticSeverity.Information;
            default               -> DiagnosticSeverity.Hint;
        };

        var lsp = new Diagnostic(range, d.getMessage(Locale.ENGLISH));
        lsp.setSeverity(severity);
        lsp.setSource("openjml");
        lsp.setCode(d.getCode());
        return lsp;
    }

    private static String baseName(String path) {
        int i = path.lastIndexOf('/');
        int j = path.lastIndexOf('\\');
        return path.substring(Math.max(i, j) + 1);
    }
}
