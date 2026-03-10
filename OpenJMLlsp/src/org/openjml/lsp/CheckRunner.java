package org.openjml.lsp;

import org.openjml.IAPI;
import org.openjml.IProverResult;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Runs OpenJML {@code --check} or {@code --esc} passes on Java/JML source
 * and returns a {@link CheckResult} containing the LSP diagnostics and the
 * OpenJML exit code.
 *
 * <p>OpenJML exit codes:
 * <ul>
 *   <li>0 — success, no issues</li>
 *   <li>1 — syntax or type errors (--check or --esc)</li>
 *   <li>2 — bad command-line arguments (indicates a bug in this server)</li>
 *   <li>6 — verification failures (--esc postcondition / assertion violations)</li>
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
     * Shared AST cache populated by every check run.
     * Accessed by {@link OpenJMLTextDocumentService} for go-to-definition.
     */
    private static final ASTCache AST_CACHE = new ASTCache();

    /** Return the shared AST cache. */
    public static ASTCache getASTCache() { return AST_CACHE; }

    /**
     * Result of a single OpenJML invocation.
     *
     * @param diagnostics      LSP diagnostics for the primary (focus) file
     * @param exitCode         raw exit code returned by {@code IAPI.execute()}
     * @param proofResults     per-method ESC results keyed by simple method name;
     *                         empty map when running {@code --check} or when no
     *                         methods were verified
     * @param foreignMessages  formatted messages from files other than the primary
     *                         file (e.g. dependency type errors); empty when there
     *                         are no cross-file issues
     */
    public record CheckResult(List<org.eclipse.lsp4j.Diagnostic> diagnostics, int exitCode,
                               Map<String, IProverResult.Kind> proofResults,
                               List<String> foreignMessages,
                               Map<String, List<org.eclipse.lsp4j.Diagnostic>> companionDiagnostics) {
        /** Returns {@code true} when OpenJML reported a catastrophic internal error. */
        public boolean isInternalError() { return exitCode == 4; }
        /** Returns {@code true} when OpenJML rejected the command line — indicates a server bug. */
        public boolean isCommandLineError() { return exitCode == 2; }
        /** Returns {@code true} when errors in other files (dependencies) prevented ESC. */
        public boolean hasForeignErrors() { return !foreignMessages.isEmpty(); }
    }

    /**
     * Collects per-method ESC proof results from OpenJML's
     * {@code IProofResultListener}.  Transient states (RUNNING, COMPLETED,
     * CANCELLED) are ignored; only the final result per method is kept.
     */
    private static class ProofResultCollector implements IAPI.IProofResultListener {
        private final Map<String, IProverResult.Kind> results = new LinkedHashMap<>();

        @Override
        public void reportProofResult(MethodSymbol msym, IProverResult result) {
            IProverResult.Kind kind = result.result();
            // Ignore transient lifecycle events — only record final outcomes.
            if (kind == IProverResult.RUNNING || kind == IProverResult.COMPLETED
                    || kind == IProverResult.CANCELLED) {
                return;
            }
            String name = msym.getSimpleName().toString();
            System.err.println("[ProofResultCollector] " + name + " -> " + kind);
            results.put(name, kind);
        }

        Map<String, IProverResult.Kind> getResults() {
            return Collections.unmodifiableMap(results);
        }
    }

    // --- public API: --check ---

    /** Run {@code --check} on in-memory content with default settings. */
    public static CheckResult check(String uri, String content) {
        return check(uri, content, new OpenJMLSettings());
    }

    /** Run {@code --check} on in-memory content. */
    public static CheckResult check(String uri, String content, OpenJMLSettings settings) {
        return runOnContent(uri, content, settings, "--check", null, false);
    }

    /**
     * Run {@code --check} on {@code content} for {@code uri}, but also make all
     * other open (possibly unsaved) files in {@code openContent} visible to the
     * compiler as in-memory source.
     *
     * <p>Each open file is written to a shared temp directory (using its base
     * name).  The temp directory is prepended to {@code settings.sourcePath} so
     * the compiler finds the in-memory versions instead of the on-disk ones.
     * This ensures that if a dependency is edited but not yet saved, checking
     * the current file still uses the up-to-date in-memory content.
     *
     * <p><b>Limitation</b>: files with identical base names but different
     * directories (e.g. two {@code Main.java} in separate packages) will collide
     * in the flat temp directory.  This is the same limitation as the single-file
     * {@link #check} path; multi-package projects require a configured
     * {@code sourcePath} with the proper directory tree.
     */
    public static CheckResult checkWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings) {
        return runOnContentWithContext(uri, content, openContent, settings, "--check", null, false);
    }

    /** Run {@code --check} on a file already on disk. */
    public static CheckResult checkFile(String filePath, String uri, OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--check", null, false);
    }

    /**
     * Check a set of modified source files together for rename validation.
     *
     * <p>Writes all modified content to a shared temp directory (named by their
     * original basenames), then runs {@code --check} on each file with
     * {@code -sourcepath} pointing to that directory so cross-file references
     * are resolved against the modified versions.
     *
     * @return merged diagnostics from all checked files (empty = rename is valid)
     */
    public static List<org.eclipse.lsp4j.Diagnostic> checkModifiedFiles(
            Map<String, String> modifiedContent, OpenJMLSettings settings) {
        Path tempDir = null;
        try {
            tempDir = Files.createTempDirectory("openjml-lsp-rename-");

            // Write all modified files at their package-relative paths.
            for (Map.Entry<String, String> e : modifiedContent.entrySet()) {
                writeToTempDir(tempDir, e.getKey(), e.getValue());
            }

            // Build a modified settings copy with sourcePath = tempDir.
            OpenJMLSettings modifiedSettings = new OpenJMLSettings();
            modifiedSettings.sourcePath  = tempDir.toString();
            modifiedSettings.specsPath   = settings.specsPath;
            modifiedSettings.solversPath = settings.solversPath;
            modifiedSettings.classPath   = settings.classPath;

            // Run --check on each file and collect all diagnostics.
            List<org.eclipse.lsp4j.Diagnostic> allDiags = new ArrayList<>();
            for (Map.Entry<String, String> e : modifiedContent.entrySet()) {
                String uri     = e.getKey();
                String content = e.getValue();
                CheckResult result = runOnContent(uri, content, modifiedSettings, "--check", null, false);
                allDiags.addAll(result.diagnostics());
            }
            return allDiags;
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

    // --- public API: --esc (multi-source) ---

    /**
     * Run {@code --esc} on a primary in-memory source file with additional
     * source files written to the same temporary directory.
     *
     * <p>All files are compiled together; only diagnostics from the primary file
     * are returned.  Type errors in any of the extra files will cause exit code 1
     * and prevent ESC from running (resulting in empty proof results).
     *
     * @param primaryUri     URI of the primary file (e.g. {@code "file:///A.java"})
     * @param primaryContent source text of the primary file
     * @param extraSources   map of filename → source text for context files
     *                       (e.g. dependencies with errors)
     */
    public static CheckResult runEscWithSources(String primaryUri, String primaryContent,
                                                 Map<String, String> extraSources) {
        return runEscWithSources(primaryUri, primaryContent, extraSources, new OpenJMLSettings());
    }

    /** Run {@code --esc} on a primary file with additional context sources. */
    public static CheckResult runEscWithSources(String primaryUri, String primaryContent,
                                                 Map<String, String> extraSources,
                                                 OpenJMLSettings settings) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);
        var prc = new ProofResultCollector();
        api.setProofResultListener(prc);

        Path tempDir = null;
        try {
            String baseName = extractBaseName(primaryUri);
            tempDir = Files.createTempDirectory("openjml-lsp-");
            Path tempFile = tempDir.resolve(baseName);
            Files.writeString(tempFile, primaryContent);

            for (Map.Entry<String, String> e : extraSources.entrySet()) {
                Files.writeString(tempDir.resolve(e.getKey()), e.getValue());
            }

            List<String> args = buildArgs(settings, "--esc");
            args.add(tempFile.toString());
            for (String fname : extraSources.keySet()) {
                args.add(tempDir.resolve(fname).toString());
            }

            logInvocation("runEscWithSources", args, primaryContent);
            int rc = api.execute(args.toArray(new String[0]));
            System.err.println("[CheckRunner.runEscWithSources] exit code " + rc);

            return new CheckResult(
                    listener.toLspDiagnostics(tempFile.toString(), primaryUri),
                    rc, prc.getResults(),
                    listener.toForeignMessages(tempFile.toString()), Map.of());
        } catch (IOException e) {
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of());
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

    // --- public API: --esc ---

    /** Run {@code --esc} on in-memory content with default settings. */
    public static CheckResult runEsc(String uri, String content) {
        return runEsc(uri, content, new OpenJMLSettings());
    }

    /** Run {@code --esc} on in-memory content. */
    public static CheckResult runEsc(String uri, String content, OpenJMLSettings settings) {
        return runOnContent(uri, content, settings, "--esc", null, true);
    }

    /** Run {@code --esc} on a single method in in-memory content with default settings. */
    public static CheckResult runEscMethod(String uri, String content, String methodName) {
        return runEscMethod(uri, content, methodName, new OpenJMLSettings());
    }

    /** Run {@code --esc} on a single method in in-memory content. */
    public static CheckResult runEscMethod(String uri, String content, String methodName,
                                           OpenJMLSettings settings) {
        return runOnContent(uri, content, settings, "--esc", methodName, true);
    }

    /** Run {@code --esc} on a file already on disk. */
    public static CheckResult runEscFile(String filePath, String uri, OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--esc", null, true);
    }

    /** Run {@code --esc} on a single method in a file already on disk. */
    public static CheckResult runEscFileMethod(String filePath, String uri, String methodName,
                                               OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--esc", methodName, true);
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

    /**
     * Like {@link #runOnContent} but writes all {@code openContent} files into
     * the same temp directory so the compiler resolves cross-file references
     * against their current in-memory versions rather than the on-disk files.
     */
    private static CheckResult runOnContentWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings,
            String modeFlag, String methodName, boolean collectProofResults) {

        var listener = new LspDiagnosticListener();
        var out      = new PrintWriter(new StringWriter());
        var api      = IAPI.make(out, listener);

        ProofResultCollector prc = null;
        if (collectProofResults) {
            prc = new ProofResultCollector();
            api.setProofResultListener(prc);
        }

        Path tempDir = null;
        try {
            tempDir = Files.createTempDirectory("openjml-lsp-");

            // Write companion open files at their package-relative paths so the
            // compiler resolves them correctly via -sourcepath.
            // tempUriToRealUri (URI-keyed) is used in the AST listener for cache updates.
            // compiledPathToRealUri (path-keyed) is built by the AST listener and used
            // for diagnostic extraction — it contains ONLY files that were actually
            // attributed by the compiler (the true set of dependencies).
            Map<String, String> tempUriToRealUri  = new java.util.HashMap<>();
            for (Map.Entry<String, String> e : openContent.entrySet()) {
                if (e.getKey().equals(uri)) continue;
                Path p = writeToTempDir(tempDir, e.getKey(), e.getValue());
                tempUriToRealUri.put(p.toUri().toString(), e.getKey());
            }

            // Write target file at its package-relative path.
            Path tempFile = writeToTempDir(tempDir, uri, content);

            // Prepend tempDir to sourcePath so in-memory versions take priority.
            OpenJMLSettings ctx = new OpenJMLSettings();
            ctx.specsPath   = settings.specsPath;
            ctx.solversPath = settings.solversPath;
            ctx.classPath   = settings.classPath;
            String orig     = settings.sourcePath != null ? settings.sourcePath : "";
            ctx.sourcePath  = orig.isEmpty()
                    ? tempDir.toString()
                    : tempDir + java.io.File.pathSeparator + orig;

            List<String> args = buildArgs(ctx, modeFlag);
            if (methodName != null && !methodName.isEmpty()) {
                args.add("--method");
                args.add(methodName);
            }
            args.add(tempFile.toString());
            logInvocation("runOnContentWithContext", args, content);

            // compiledPathToRealUri is populated by the AST listener — only files
            // that were actually attributed get an entry.  Start with the target.
            final Map<String, String> compiledPathToRealUri = new java.util.concurrent.ConcurrentHashMap<>();
            compiledPathToRealUri.put(tempFile.toString(), uri);

            final String tempTargetUri = tempFile.toUri().toString();
            IAPI.IASTListener astListener = (astCtx, jfo, ast) -> {
                String jfoUri = jfo.toUri().toString();
                if (jfoUri.equals(tempTargetUri)) {
                    AST_CACHE.put(uri, astCtx, (JmlCompilationUnit) ast);
                } else {
                    String realUri = tempUriToRealUri.get(jfoUri);
                    if (realUri != null) {
                        AST_CACHE.put(realUri, astCtx, (JmlCompilationUnit) ast);
                        // Record that this file was compiled so we can extract its diags.
                        try {
                            Path p = java.nio.file.Paths.get(java.net.URI.create(jfoUri));
                            compiledPathToRealUri.put(p.toString(), realUri);
                        } catch (Exception ignored) {}
                    }
                }
            };
            IAPI.setASTListener(astListener);
            int rc;
            try {
                rc = api.execute(args.toArray(new String[0]));
            } finally {
                IAPI.removeASTListener(astListener);
            }
            System.err.println("[CheckRunner.runOnContentWithContext] exit code " + rc
                    + " (" + modeFlag + ")");

            Map<String, IProverResult.Kind> proofResults =
                    prc != null ? prc.getResults() : Map.of();
            // Extract diagnostics for the target AND all files that were actually compiled.
            Map<String, List<org.eclipse.lsp4j.Diagnostic>> allDiags =
                    listener.toLspDiagnosticsAll(compiledPathToRealUri);
            List<org.eclipse.lsp4j.Diagnostic> primaryDiags =
                    allDiags.getOrDefault(uri, List.of());
            allDiags.remove(uri);   // companions = everything except the primary
            return new CheckResult(primaryDiags, rc, proofResults,
                    listener.toForeignMessages(tempFile.toString()), allDiags);
        } catch (IOException e) {
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of());
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

    private static CheckResult runOnContent(
            String uri, String content, OpenJMLSettings settings, String modeFlag,
            String methodName, boolean collectProofResults) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);

        ProofResultCollector prc = null;
        if (collectProofResults) {
            prc = new ProofResultCollector();
            api.setProofResultListener(prc);
        }

        Path tempDir = null;
        try {
            tempDir = Files.createTempDirectory("openjml-lsp-");
            Path tempFile = writeToTempDir(tempDir, uri, content);

            List<String> args = buildArgs(settings, modeFlag);
            if (methodName != null && !methodName.isEmpty()) {
                args.add("--method");
                args.add(methodName);
            }
            args.add(tempFile.toString());
            logInvocation("runOnContent", args, content);

            // Register an AST listener that remaps the temp-file URI to the caller's URI.
            final String tempUriStr = tempFile.toUri().toString();
            final String callerUri  = uri;
            IAPI.IASTListener astListener = (ctx, jfo, ast) -> {
                if (jfo.toUri().toString().equals(tempUriStr))
                    AST_CACHE.put(callerUri, ctx, (JmlCompilationUnit) ast);
            };
            IAPI.setASTListener(astListener);
            int rc;
            try {
                rc = api.execute(args.toArray(new String[0]));
            } finally {
                IAPI.removeASTListener(astListener);
            }
            System.err.println("[CheckRunner.runOnContent] exit code " + rc
                    + " (" + modeFlag + ")");

            Map<String, IProverResult.Kind> proofResults =
                    prc != null ? prc.getResults() : Map.of();
            return new CheckResult(listener.toLspDiagnostics(tempFile.toString(), uri), rc,
                    proofResults, listener.toForeignMessages(tempFile.toString()), Map.of());
        } catch (IOException e) {
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of());
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
            String methodName, boolean collectProofResults) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);

        ProofResultCollector prc = null;
        if (collectProofResults) {
            prc = new ProofResultCollector();
            api.setProofResultListener(prc);
        }

        List<String> args = buildArgs(settings, modeFlag);
        if (methodName != null && !methodName.isEmpty()) {
            args.add("--method");
            args.add(methodName);
        }
        args.add(filePath);
        logInvocation("runOnFile", args);

        // Register an AST listener that stores each attributed file under its own URI.
        // When additional files are compiled via -sourcepath, each gets its own cache
        // entry — enabling cross-file go-to-definition within the same IAPI context.
        IAPI.IASTListener astListener = (ctx, jfo, ast) ->
                AST_CACHE.put(jfo.toUri().toString(), ctx, (JmlCompilationUnit) ast);
        IAPI.setASTListener(astListener);
        int rc;
        try {
            rc = api.execute(args.toArray(new String[0]));
        } finally {
            IAPI.removeASTListener(astListener);
        }
        System.err.println("[CheckRunner.runOnFile] exit code " + rc
                + " (" + modeFlag + ")");

        Map<String, IProverResult.Kind> proofResults =
                prc != null ? prc.getResults() : Map.of();
        return new CheckResult(listener.toLspDiagnostics(filePath, uri), rc,
                proofResults, listener.toForeignMessages(filePath), Map.of());
    }

    /**
     * Run {@code --check} on all {@code filePaths} in a single OpenJML invocation,
     * populating the AST cache for every successfully attributed file.
     *
     * <p>Diagnostics are discarded — the purpose is to build the workspace symbol
     * index so that {@code workspace/symbol} can find declarations in non-open files.
     * Called in a background thread after the LSP {@code initialized} handshake.
     *
     * @param filePaths absolute paths of all {@code .java} files to index
     * @param settings  current OpenJML settings (specs path, solvers path, etc.)
     */
    public static void indexWorkspaceFiles(List<String> filePaths, OpenJMLSettings settings) {
        if (filePaths.isEmpty()) return;
        var out      = new PrintWriter(new StringWriter());
        var listener = new LspDiagnosticListener();  // diagnostics discarded
        var api      = IAPI.make(out, listener);

        List<String> args = buildArgs(settings, "--check");
        filePaths.forEach(args::add);
        logInvocation("indexWorkspaceFiles", args);

        AST_CACHE.setIndexing(true);
        IAPI.IASTListener astListener = (ctx, jfo, ast) ->
                AST_CACHE.putInit(jfo.toUri().toString(), ctx, (JmlCompilationUnit) ast);
        IAPI.setASTListener(astListener);
        try {
            api.execute(args.toArray(new String[0]));
        } finally {
            IAPI.removeASTListener(astListener);
            AST_CACHE.setIndexing(false);
        }
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

    /**
     * Extract the package name from Java/JML source content, or {@code ""} for
     * the default package.  Only the first {@code package} keyword is examined;
     * the search stops at the first {@code class} or {@code interface} keyword so
     * that {@code package} appearing in a string literal or comment after the
     * class declaration is ignored.
     */
    static String extractPackage(String source) {
        java.util.regex.Matcher m = java.util.regex.Pattern
                .compile("(?s)^.*?(?=class|interface|enum|@interface)")
                .matcher(source);
        String header = m.find() ? m.group() : source;
        java.util.regex.Matcher pkg = java.util.regex.Pattern
                .compile("\\bpackage\\s+([\\w.]+)\\s*;")
                .matcher(header);
        return pkg.find() ? pkg.group(1) : "";
    }

    /**
     * Write {@code content} to {@code tempDir} at the path implied by its
     * package declaration and base name, creating intermediate directories.
     * Returns the {@link Path} of the written file.
     *
     * <p>Example: {@code package com.example; class Foo} in {@code Foo.java}
     * → {@code tempDir/com/example/Foo.java}.
     */
    static Path writeToTempDir(Path tempDir, String uri, String content) throws IOException {
        String pkg      = extractPackage(content);
        String baseName = extractBaseName(uri);
        Path   dir      = pkg.isEmpty()
                ? tempDir
                : tempDir.resolve(pkg.replace('.', java.io.File.separatorChar));
        Files.createDirectories(dir);
        Path file = dir.resolve(baseName);
        Files.writeString(file, content);
        return file;
    }
}
