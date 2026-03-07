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
 * Position conventions:
 *   - javax.tools.Diagnostic: 1-indexed lines and columns; -1 means unknown
 *   - LSP: 0-indexed lines and columns
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

        var position = new Position(lspLine, lspCol);
        var range    = new Range(position, position);  // point range

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
