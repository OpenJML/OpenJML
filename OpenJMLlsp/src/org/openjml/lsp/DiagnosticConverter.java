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
 *   <li>javax.tools.Diagnostic: 1-indexed line/column; {@code NOPOS} (-1) means unknown</li>
 *   <li>LSP: 0-indexed lines and columns</li>
 * </ul>
 *
 * <p>When the diagnostic carries valid {@code startPosition} and {@code endPosition}
 * character offsets, the end column is computed as
 * {@code startColumn + (endPosition - startPosition)}, keeping the range on the
 * same line as the start.  This gives editors a squiggly underline covering the
 * offending token or expression without requiring the source text.
 * If the offsets are unavailable, a point range at the reported line/column is used.
 */
public class DiagnosticConverter {

    public static Diagnostic convert(
            javax.tools.Diagnostic<? extends JavaFileObject> d,
            String sourcePath,
            String targetUri) {

        // Skip diagnostics from files other than the one being checked.
        // DiagnosticListener can receive errors from transitively loaded files.
        if (d.getSource() != null && sourcePath != null) {
            String srcName = d.getSource().getName();
            if (!srcName.isEmpty() && !srcName.endsWith(baseName(sourcePath))) {
                return null;
            }
        }

        long line = d.getLineNumber();
        long col  = d.getColumnNumber();

        // Convert from 1-indexed to 0-indexed; clamp negatives to 0
        int lspLine = line > 0 ? (int)(line - 1) : 0;
        int lspCol  = col  > 0 ? (int)(col  - 1) : 0;

        long startPos = d.getStartPosition();
        long endPos   = d.getEndPosition();

        Range range;
        if (startPos != javax.tools.Diagnostic.NOPOS
                && endPos   != javax.tools.Diagnostic.NOPOS
                && endPos   >= startPos) {
            // Expand the end column by the span length, staying on the same line.
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
