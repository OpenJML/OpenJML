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
 * and returns a {@link CheckResult} containing the LSP diagnostics and the
 * OpenJML exit code.
 *
 * <p>OpenJML exit codes:
 * <ul>
 *   <li>0 — success, no issues</li>
 *   <li>1 — warnings only</li>
 *   <li>2 — errors (type or verification failures)</li>
 *   <li>4 — internal / catastrophic error</li>
 * </ul>
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

    /**
     * Result of a single OpenJML invocation.
     *
     * @param diagnostics  LSP diagnostics collected by the listener
     * @param exitCode     raw exit code returned by {@code IAPI.execute()}
     */
    public record CheckResult(List<org.eclipse.lsp4j.Diagnostic> diagnostics, int exitCode) {
        /** Returns {@code true} when OpenJML reported a catastrophic internal error. */
        public boolean isInternalError() { return exitCode == 4; }
    }

    // --- public API: --check ---

    /** Run {@code --check} on in-memory content with default settings. */
    public static CheckResult check(String uri, String content) {
        return check(uri, content, new OpenJMLSettings());
    }

    /** Run {@code --check} on in-memory content. */
    public static CheckResult check(String uri, String content, OpenJMLSettings settings) {
        return runOnContent(uri, content, settings, "--check", null);
    }

    /** Run {@code --check} on a file already on disk. */
    public static CheckResult checkFile(String filePath, String uri, OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--check", null);
    }

    // --- public API: --esc ---

    /** Run {@code --esc} on in-memory content with default settings. */
    public static CheckResult runEsc(String uri, String content) {
        return runEsc(uri, content, new OpenJMLSettings());
    }

    /** Run {@code --esc} on in-memory content. */
    public static CheckResult runEsc(String uri, String content, OpenJMLSettings settings) {
        return runOnContent(uri, content, settings, "--esc", null);
    }

    /** Run {@code --esc} on a single method in in-memory content with default settings. */
    public static CheckResult runEscMethod(String uri, String content, String methodName) {
        return runEscMethod(uri, content, methodName, new OpenJMLSettings());
    }

    /** Run {@code --esc} on a single method in in-memory content. */
    public static CheckResult runEscMethod(String uri, String content, String methodName,
                                           OpenJMLSettings settings) {
        return runOnContent(uri, content, settings, "--esc", methodName);
    }

    /** Run {@code --esc} on a file already on disk. */
    public static CheckResult runEscFile(String filePath, String uri, OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--esc", null);
    }

    /** Run {@code --esc} on a single method in a file already on disk. */
    public static CheckResult runEscFileMethod(String filePath, String uri, String methodName,
                                               OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--esc", methodName);
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

    private static CheckResult runOnContent(
            String uri, String content, OpenJMLSettings settings, String modeFlag,
            String methodName) {
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
            if (methodName != null && !methodName.isEmpty()) {
                args.add("--method");
                args.add(methodName);
            }
            args.add(tempFile.toString());
            logInvocation("runOnContent", args, content);
            int rc = api.execute(args.toArray(new String[0]));
            System.err.println("[CheckRunner.runOnContent] exit code " + rc
                    + " (" + modeFlag + ")");

            return new CheckResult(listener.toLspDiagnostics(tempFile.toString(), uri), rc);
        } catch (IOException e) {
            return new CheckResult(List.of(), -1);
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

    private static CheckResult runOnFile(
            String filePath, String uri, OpenJMLSettings settings, String modeFlag,
            String methodName) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);

        List<String> args = buildArgs(settings, modeFlag);
        if (methodName != null && !methodName.isEmpty()) {
            args.add("--method");
            args.add(methodName);
        }
        args.add(filePath);
        logInvocation("runOnFile", args);
        int rc = api.execute(args.toArray(new String[0]));
        System.err.println("[CheckRunner.runOnFile] exit code " + rc
                + " (" + modeFlag + ")");

        return new CheckResult(listener.toLspDiagnostics(filePath, uri), rc);
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

    /** Log an OpenJML invocation to stderr (captured in /tmp/openjml-lsp-debug.log). */
    private static void logInvocation(String caller, List<String> args) {
        logInvocation(caller, args, null);
    }

    private static void logInvocation(String caller, List<String> args, String content) {
        StringBuilder sb = new StringBuilder();
        sb.append("[CheckRunner.").append(caller).append("] args:");
        for (String a : args) sb.append(' ').append(a);
        sb.append('\n');
        if (content != null) {
            int nl = content.indexOf('\n');
            String firstLine = nl >= 0 ? content.substring(0, nl) : content;
            String preview = content.length() <= 1000
                    ? content
                    : content.substring(0, 1000) + "...[truncated]";
            sb.append("  content: ").append(content.length()).append(" chars, first line: ")
              .append(firstLine).append('\n');
            sb.append("  content preview:\n").append(preview).append('\n');
        }
        sb.append("  OPENJML_INSTALL=").append(System.getenv("OPENJML_INSTALL")).append('\n');
        sb.append("  OPENJML_SPECS=").append(System.getenv("OPENJML_SPECS")).append('\n');
        sb.append("  OPENJML_SOLVERS=").append(System.getenv("OPENJML_SOLVERS")).append('\n');
        System.err.print(sb);
    }

    private static String extractBaseName(String uri) {
        int slash = Math.max(uri.lastIndexOf('/'), uri.lastIndexOf('\\'));
        String name = slash >= 0 ? uri.substring(slash + 1) : uri;
        if (!name.endsWith(".java")) name = name.replaceAll("[^A-Za-z0-9_]", "_") + ".java";
        return name;
    }
}
