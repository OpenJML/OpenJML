package org.openjml.lsp;

import org.openjml.IAPI;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
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
     * Check the given source content using default settings and return LSP diagnostics.
     *
     * @param uri     the LSP document URI (used to label diagnostics)
     * @param content the current source text
     * @return list of LSP Diagnostic objects; empty on I/O failure
     */
    public static List<org.eclipse.lsp4j.Diagnostic> check(String uri, String content) {
        return check(uri, content, new OpenJMLSettings());
    }

    /**
     * Check the given source content and return LSP diagnostics.
     *
     * @param uri      the LSP document URI (used to label diagnostics)
     * @param content  the current source text
     * @param settings user-configured options (specs path, solvers path, mode)
     * @return list of LSP Diagnostic objects; empty on I/O failure
     */
    public static List<org.eclipse.lsp4j.Diagnostic> check(String uri, String content,
                                                            OpenJMLSettings settings) {
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

            List<String> args = buildArgs(settings);
            args.add(tempFile.toString());
            api.execute(args.toArray(new String[0]));

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

    /**
     * Check a file that is already on disk (e.g., just opened or just saved).
     * Passes the real file path to OpenJML — no temp file needed.
     *
     * @param filePath absolute path of the file on disk
     * @param uri      the LSP document URI (used to label diagnostics)
     * @param settings user-configured options
     * @return list of LSP Diagnostic objects; empty on error
     */
    public static List<org.eclipse.lsp4j.Diagnostic> checkFile(String filePath, String uri,
                                                                OpenJMLSettings settings) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);

        List<String> args = buildArgs(settings);
        args.add(filePath);
        api.execute(args.toArray(new String[0]));

        return listener.toLspDiagnostics(filePath, uri);
    }

    /**
     * Convert a {@code file://} URI to an absolute file path, or {@code null}
     * if the URI is not a file URI or cannot be parsed.
     */
    public static String uriToPath(String uri) {
        try {
            return URI.create(uri).getPath();
        } catch (Exception e) {
            return null;
        }
    }

    private static List<String> buildArgs(OpenJMLSettings settings) {
        List<String> args = new ArrayList<>();
        args.add(settings.modeFlag());
        if (settings.specsPath != null && !settings.specsPath.isEmpty()) {
            args.add("--specs-path");
            args.add(settings.specsPath);
        }
        if (settings.solversPath != null && !settings.solversPath.isEmpty()) {
            args.add("--solvers-path");
            args.add(settings.solversPath);
        }
        if (settings.sourcePath != null && !settings.sourcePath.isEmpty()) {
            args.add("-sourcepath");
            args.add(settings.sourcePath);
        }
        if (settings.classPath != null && !settings.classPath.isEmpty()) {
            args.add("-classpath");
            args.add(settings.classPath);
        }
        return args;
    }

    private static String extractBaseName(String uri) {
        int slash = Math.max(uri.lastIndexOf('/'), uri.lastIndexOf('\\'));
        String name = slash >= 0 ? uri.substring(slash + 1) : uri;
        // Ensure the name ends with .java so OpenJML handles it as Java source.
        if (!name.endsWith(".java")) name = name.replaceAll("[^A-Za-z0-9_]", "_") + ".java";
        return name;
    }
}
