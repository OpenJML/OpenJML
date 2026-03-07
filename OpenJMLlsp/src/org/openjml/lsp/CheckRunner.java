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
 * Runs OpenJML {@code --check} or {@code --esc} passes on Java/JML source
 * and returns LSP diagnostics.
 *
 * Each call creates a fresh OpenJML compilation context (fresh {@code IAPI})
 * to avoid shared state between checks.
 *
 * In-memory content is written to a temporary file so that javac's
 * public-class-name check passes.  The temp file is deleted after the check.
 * When the file already exists on disk (open/save case), its path is passed
 * directly to OpenJML — no temp file needed.
 */
public class CheckRunner {

    // --- public API: --check ---

    /** Run {@code --check} on in-memory content with default settings. */
    public static List<org.eclipse.lsp4j.Diagnostic> check(String uri, String content) {
        return check(uri, content, new OpenJMLSettings());
    }

    /** Run {@code --check} on in-memory content. */
    public static List<org.eclipse.lsp4j.Diagnostic> check(String uri, String content,
                                                            OpenJMLSettings settings) {
        return runOnContent(uri, content, settings, "--check");
    }

    /** Run {@code --check} on a file already on disk. */
    public static List<org.eclipse.lsp4j.Diagnostic> checkFile(String filePath, String uri,
                                                                OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--check");
    }

    // --- public API: --esc ---

    /** Run {@code --esc} on in-memory content with default settings. */
    public static List<org.eclipse.lsp4j.Diagnostic> runEsc(String uri, String content) {
        return runEsc(uri, content, new OpenJMLSettings());
    }

    /** Run {@code --esc} on in-memory content. */
    public static List<org.eclipse.lsp4j.Diagnostic> runEsc(String uri, String content,
                                                             OpenJMLSettings settings) {
        return runOnContent(uri, content, settings, "--esc");
    }

    /** Run {@code --esc} on a file already on disk. */
    public static List<org.eclipse.lsp4j.Diagnostic> runEscFile(String filePath, String uri,
                                                                 OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--esc");
    }

    // --- utility ---

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

    // --- private implementation ---

    private static List<org.eclipse.lsp4j.Diagnostic> runOnContent(
            String uri, String content, OpenJMLSettings settings, String modeFlag) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);

        Path tempDir = null;
        try {
            String baseName = extractBaseName(uri);
            tempDir = Files.createTempDirectory("openjml-lsp-");
            Path tempFile = tempDir.resolve(baseName);
            Files.writeString(tempFile, content);

            List<String> args = buildArgs(settings, modeFlag);
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

    private static List<org.eclipse.lsp4j.Diagnostic> runOnFile(
            String filePath, String uri, OpenJMLSettings settings, String modeFlag) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);

        List<String> args = buildArgs(settings, modeFlag);
        args.add(filePath);
        api.execute(args.toArray(new String[0]));

        return listener.toLspDiagnostics(filePath, uri);
    }

    private static List<String> buildArgs(OpenJMLSettings settings, String modeFlag) {
        List<String> args = new ArrayList<>();
        args.add(modeFlag);
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
        if (!name.endsWith(".java")) name = name.replaceAll("[^A-Za-z0-9_]", "_") + ".java";
        return name;
    }
}
