package org.openjml.lsp;

import org.openjml.IAPI;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.List;

/**
 * Runs an OpenJML {@code --check} pass on Java/JML source content and
 * returns LSP diagnostics.
 *
 * Each call creates a fresh OpenJML compilation context (fresh {@code IAPI})
 * to avoid any shared state between checks.
 *
 * Because the current {@code IAPI.execute()} API accepts file paths, in-memory
 * content is written to a temporary file, checked, and then deleted.  The
 * temp-file path is remapped back to the original document URI in the
 * returned diagnostics.
 */
public class CheckRunner {

    /**
     * Check the given source content and return LSP diagnostics.
     *
     * @param uri     the LSP document URI (used to label diagnostics)
     * @param content the current source text
     * @return list of LSP Diagnostic objects; empty on I/O failure
     */
    public static List<org.eclipse.lsp4j.Diagnostic> check(String uri, String content) {
        var listener = new LspDiagnosticListener();
        // Discard non-diagnostic output; diagnostics come through the listener.
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);

        // Write the content into a temp directory using the exact base name from
        // the URI so that javac's public-class-name check passes (e.g. Clean.java).
        Path tempDir = null;
        try {
            String baseName = extractBaseName(uri);
            tempDir = Files.createTempDirectory("openjml-lsp-");
            Path tempFile = tempDir.resolve(baseName);
            Files.writeString(tempFile, content);

            api.execute("--check", tempFile.toString());

            return listener.toLspDiagnostics(tempFile.toString(), uri);
        } catch (IOException e) {
            return List.of();
        } finally {
            if (tempDir != null) {
                try {
                    Files.walk(tempDir)
                         .sorted(Comparator.reverseOrder())
                         .forEach(p -> { try { Files.delete(p); } catch (IOException ignored) {} });
                } catch (IOException ignored) {}
            }
        }
    }

    private static String extractBaseName(String uri) {
        int slash = Math.max(uri.lastIndexOf('/'), uri.lastIndexOf('\\'));
        String name = slash >= 0 ? uri.substring(slash + 1) : uri;
        // Ensure the name ends with .java so OpenJML handles it as Java source.
        if (!name.endsWith(".java")) name = name.replaceAll("[^A-Za-z0-9_]", "_") + ".java";
        return name;
    }
}
