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
    /**
     * Return the names of files OTHER than the primary {@code sourcePath} that
     * produced at least one diagnostic (i.e. dependency files whose errors
     * prevented compilation).  Each entry is a plain filename such as
     * {@code "B.java"}, in the order first seen, without duplicates.
     */
    public List<String> toForeignMessages(String sourcePath) {
        String base = baseName(sourcePath);
        List<String> files = new ArrayList<>();
        java.util.Set<String> seen = new java.util.LinkedHashSet<>();
        for (var d : collected) {
            if (d.getSource() == null) continue;
            String srcName = d.getSource().getName();
            if (srcName.isEmpty() || srcName.endsWith(base)) continue;
            String fileName = baseName(srcName);
            if (seen.add(fileName)) files.add(fileName);
        }
        return files;
    }

    private static String baseName(String path) {
        int i = Math.max(path.lastIndexOf('/'), path.lastIndexOf('\\'));
        return path.substring(i + 1);
    }

    public List<org.eclipse.lsp4j.Diagnostic> toLspDiagnostics(String sourcePath, String targetUri) {
        System.err.println("[LspDiagnosticListener] " + collected.size()
                + " raw diagnostic(s) for " + sourcePath);
        var result = new ArrayList<org.eclipse.lsp4j.Diagnostic>();
        for (var d : collected) {
            String src = d.getSource() == null ? "<null>" : d.getSource().getName();
            System.err.println("  raw: kind=" + d.getKind()
                    + " code=" + d.getCode()
                    + " line=" + d.getLineNumber()
                    + " src=" + src
                    + " msg=" + d.getMessage(java.util.Locale.ENGLISH));
            var lsp = DiagnosticConverter.convert(d, sourcePath, targetUri);
            if (lsp != null) {
                result.add(lsp);
            } else {
                System.err.println("    ^ filtered out by DiagnosticConverter");
            }
        }
        System.err.println("[LspDiagnosticListener] " + result.size() + " LSP diagnostic(s) after filtering");
        return result;
    }
}
