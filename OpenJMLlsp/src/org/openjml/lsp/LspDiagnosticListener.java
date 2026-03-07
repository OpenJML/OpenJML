package org.openjml.lsp;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;
import javax.tools.JavaFileObject;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Collects all diagnostics emitted by OpenJML during a check pass,
 * then converts them to LSP Diagnostic objects on request.
 */
public class LspDiagnosticListener implements DiagnosticListener<JavaFileObject> {

    private final List<Diagnostic<? extends JavaFileObject>> collected =
            Collections.synchronizedList(new ArrayList<Diagnostic<? extends JavaFileObject>>());

    @Override
    public void report(Diagnostic<? extends JavaFileObject> diagnostic) {
        collected.add(diagnostic);
    }

    public List<Diagnostic<? extends JavaFileObject>> getDiagnostics() {
        return Collections.unmodifiableList(collected);
    }

    /**
     * Convert collected diagnostics to LSP Diagnostics.
     *
     * @param sourcePath the temp-file path actually passed to OpenJML (for filtering)
     * @param targetUri  the LSP document URI to report diagnostics against
     */
    public List<org.eclipse.lsp4j.Diagnostic> toLspDiagnostics(String sourcePath, String targetUri) {
        var result = new ArrayList<org.eclipse.lsp4j.Diagnostic>();
        for (var d : collected) {
            var lsp = DiagnosticConverter.convert(d, sourcePath, targetUri);
            if (lsp != null) result.add(lsp);
        }
        return result;
    }
}
