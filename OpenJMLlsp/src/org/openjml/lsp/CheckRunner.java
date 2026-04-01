package org.openjml.lsp;

import org.openjml.IAPI;
import org.openjml.IProverResult;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

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
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.function.Consumer;

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

    // ---- Output-channel logging ----

    private static volatile java.util.function.Consumer<String> logCallback = null;

    /** Set the callback that receives user-visible log lines (routed to the VS Code Output channel). */
    public static void setLogCallback(java.util.function.Consumer<String> cb) { logCallback = cb; }

    private static void log(String msg) {
        java.util.function.Consumer<String> cb = logCallback;
        if (cb != null) cb.accept(msg);
    }

    private static String ts() {
        return "[" + java.time.LocalTime.now()
                .format(java.time.format.DateTimeFormatter.ofPattern("HH:mm:ss")) + "] ";
    }

    /** Return just the file name portion of a URI or path (no directory). */
    private static String fileName(String uri) {
        int slash = Math.max(uri.lastIndexOf('/'), uri.lastIndexOf('\\'));
        return slash >= 0 ? uri.substring(slash + 1) : uri;
    }

    /** Translate a raw proof-result kind to a user-friendly label. */
    private static String kindLabel(IProverResult.Kind kind) {
        if (kind == null)              return "unknown";
        if (kind == IProverResult.UNSAT) return "Verified";
        if (kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT) return "Not Verified";
        return kind.toString();
    }

    /** Log ESC proof results from a subprocess (--esc) run. */
    private static void logEscResults(String fname,
                                      Map<String, IProverResult.Kind> proofResults,
                                      int numDiags) {
        if (!proofResults.isEmpty()) {
            for (Map.Entry<String, IProverResult.Kind> e : proofResults.entrySet())
                log(ts() + " --esc " + fname + " " + e.getKey() + ": " + kindLabel(e.getValue()));
        } else {
            log(ts() + " --esc " + fname + ": " + numDiags + " diagnostic(s)");
        }
    }

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
                               Map<String, List<org.eclipse.lsp4j.Diagnostic>> allDiagnostics) {
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

    /**
     * Result of a multi-path {@code --dirs} ESC invocation.
     *
     * @param diagnosticsByUri  LSP diagnostics grouped by the {@code file://} URI of
     *                          each source file that produced at least one diagnostic;
     *                          files with no issues are absent from the map
     * @param exitCode          raw exit code from {@code IAPI.execute()}
     * @param proofResults      per-method ESC results keyed by simple method name
     */
    public record DirCheckResult(
            Map<String, List<org.eclipse.lsp4j.Diagnostic>> diagnosticsByUri,
            int exitCode,
            Map<String, IProverResult.Kind> proofResults) {}

    /**
     * Run {@code --esc --dirs path1 path2 ...} on one or more files or directories.
     *
     * <p>Each path may be a {@code .java} file or a directory; OpenJML processes
     * directory arguments recursively (same behaviour as repeated {@code --dir}).
     * Diagnostics are returned grouped by source-file URI so the caller can
     * publish them to the correct LSP document.
     */
    /**
     * Run {@code --check --dirs path1 path2 ...} on one or more files or directories.
     * Returns diagnostics grouped by source-file URI.
     */
    public static DirCheckResult runCheckDir(List<String> paths, OpenJMLSettings settings) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);
        List<String> args = buildArgs(settings, "--check");
        args.add("--dirs");
        args.addAll(paths);
        logInvocation("runCheckDir", args);
        int rc = api.execute(args.toArray(new String[0]));
        System.err.println("[CheckRunner.runCheckDir] exit code " + rc
                + " for " + paths.size() + " path(s)");
        return new DirCheckResult(listener.toLspDiagnosticsByFile(), rc, Map.of());
    }

    public static DirCheckResult runEscDir(List<String> paths, OpenJMLSettings settings) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);
        var prc = new ProofResultCollector();
        api.setProofResultListener(prc);

        List<String> args = buildArgs(settings, "--esc");
        args.add("--dirs");
        args.addAll(paths);
        logInvocation("runEscDir", args);
        int rc = api.execute(args.toArray(new String[0]));
        System.err.println("[CheckRunner.runEscDir] exit code " + rc
                + " for " + paths.size() + " path(s)");

        return new DirCheckResult(listener.toLspDiagnosticsByFile(), rc, prc.getResults());
    }

    /**
     * Run {@code --rac --dirs path1 path2 ...} on one or more files or directories.
     *
     * <p>The output directory is taken from {@link OpenJMLSettings#racOutputDir}
     * (resolved relative to the first workspace folder when relative, defaulting to
     * {@code rac-classes} when absent).  The directory is created if it does not exist.
     *
     * <p>Returns a {@link CheckResult} whose {@link CheckResult#allDiagnostics()} map
     * contains diagnostics grouped by source-file URI.
     */
    public static CheckResult runRacPaths(List<String> paths, OpenJMLSettings settings) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);

        List<String> args = buildArgs(settings, "--rac");

        // Resolve and create the RAC output directory.
        String rawDir = (settings.racOutputDir != null && !settings.racOutputDir.isEmpty())
                ? settings.racOutputDir : "rac-classes";
        java.nio.file.Path raw = java.nio.file.Paths.get(rawDir);
        java.nio.file.Path outputPath;
        if (raw.isAbsolute()) {
            outputPath = raw;
        } else {
            String wsRoot = (settings.workspaceFolderPaths != null
                    && !settings.workspaceFolderPaths.isEmpty())
                    ? settings.workspaceFolderPaths.split(java.io.File.pathSeparator)[0]
                    : ".";
            outputPath = java.nio.file.Paths.get(wsRoot).resolve(raw);
        }
        try { java.nio.file.Files.createDirectories(outputPath); }
        catch (java.io.IOException e) {
            System.err.println("[CheckRunner.runRacPaths] failed to create output dir: " + e);
        }
        args.add("-d");
        args.add(outputPath.toString());
        args.add("--dirs");
        args.addAll(paths);
        logInvocation("runRacPaths", args);
        int rc = api.execute(args.toArray(new String[0]));
        System.err.println("[CheckRunner.runRacPaths] exit code " + rc
                + " for " + paths.size() + " path(s)");

        return new CheckResult(List.of(), rc, Map.of(), List.of(),
                listener.toLspDiagnosticsByFile());
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

            // Write all modified files at their package-relative paths and record the mapping.
            Map<String, String> tempPathToRealUri = new java.util.LinkedHashMap<>();
            List<String> filePaths = new ArrayList<>();
            for (Map.Entry<String, String> e : modifiedContent.entrySet()) {
                Path p = writeToTempDir(tempDir, e.getKey(), e.getValue());
                tempPathToRealUri.put(p.toString(), e.getKey());
                filePaths.add(p.toString());
            }

            // Use tempDir as the sole sourcepath entry.  All modified files have already
            // been written there, so javac resolves every cross-file reference against the
            // modified versions.  Including the original settings.sourcePath here would add
            // the unmodified testdata/source directory alongside tempDir; since all file
            // basenames are the same (e.g., IWorker.java in both tempDir and testdata), javac
            // can see the same class from two sources and fail silently with a duplicate-class
            // conflict, losing the diagnostics we need to detect rename errors.
            OpenJMLSettings modifiedSettings = new OpenJMLSettings();
            modifiedSettings.sourcePath      = tempDir.toString();
            modifiedSettings.specsPath       = buildEffectiveSpecsPath(tempDir, settings);
            modifiedSettings.solversPath     = settings.solversPath;
            modifiedSettings.classPath       = settings.classPath;
            // workspaceFolderPaths already baked into sourcePath above.

            // Run a single --check invocation on all files so cross-file dependencies
            // (e.g., A.java referencing a renamed symbol in B.java) are caught.
            var listener = new LspDiagnosticListener();
            var out = new java.io.PrintWriter(new java.io.StringWriter());
            var api = IAPI.make(out, listener);
            List<String> args = buildArgs(modifiedSettings, "--check");
            args.addAll(filePaths);
            logInvocation("checkModifiedFiles", args);
            try {
                api.execute(args.toArray(new String[0]));
            } catch (Throwable t) {
                System.err.println("[CheckRunner.checkModifiedFiles] execute failed: " + t);
            }

            // Collect all diagnostics across files.
            List<org.eclipse.lsp4j.Diagnostic> allDiags = new ArrayList<>();
            for (List<org.eclipse.lsp4j.Diagnostic> diags :
                    listener.toLspDiagnosticsAll(tempPathToRealUri).values()) {
                allDiags.addAll(diags);
            }
            return allDiags;
        } catch (IOException e) {
            System.err.println("[CheckRunner.checkModifiedFiles] I/O error: " + e);
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
     * Result of a multi-file {@code --check} run that also captures a fresh
     * {@link ASTCache} populated with the attributed ASTs of the modified sources.
     * Used by {@link Renamer} for reference-stability validation.
     *
     * @param diagnostics       merged diagnostics from all checked files
     * @param cache             fresh AST cache keyed by temp-dir absolute paths
     * @param tempPathToRealUri maps temp-dir absolute paths to the caller's real URIs
     */
    public record CheckAndCacheResult(
            List<org.eclipse.lsp4j.Diagnostic> diagnostics,
            ASTCache cache,
            Map<String, String> tempPathToRealUri) {}

    /**
     * Like {@link #checkModifiedFiles} but also captures a fresh {@link ASTCache}
     * populated with the attributed ASTs of every modified file.
     *
     * <p>The returned {@link CheckAndCacheResult#cache()} is keyed by temp-dir
     * absolute paths (the same keys as {@link CheckAndCacheResult#tempPathToRealUri()}).
     * Pass those paths — and a content map keyed by the same paths — to
     * {@link ReferenceFinder#findReferences} to query references in the modified
     * compilation without touching the shared {@link #AST_CACHE}.
     *
     * <p>Used by {@link Renamer} for step 4.5 reference-stability validation.
     */
    public static CheckAndCacheResult checkModifiedFilesAndGetCache(
            Map<String, String> modifiedContent, OpenJMLSettings settings) {
        Path tempDir = null;
        try {
            tempDir = Files.createTempDirectory("openjml-lsp-rename-");

            Map<String, String> tempPathToRealUri = new java.util.LinkedHashMap<>();
            List<String> filePaths = new ArrayList<>();
            for (Map.Entry<String, String> e : modifiedContent.entrySet()) {
                Path p = writeToTempDir(tempDir, e.getKey(), e.getValue());
                tempPathToRealUri.put(p.toString(), e.getKey());
                filePaths.add(p.toString());
            }

            OpenJMLSettings modifiedSettings = new OpenJMLSettings();
            modifiedSettings.sourcePath  = buildEffectiveSourcePath(tempDir, settings);
            modifiedSettings.specsPath   = buildEffectiveSpecsPath(tempDir, settings);
            modifiedSettings.solversPath = settings.solversPath;
            modifiedSettings.classPath   = settings.classPath;

            var listener = new LspDiagnosticListener();
            var out = new java.io.PrintWriter(new java.io.StringWriter());
            var api = IAPI.make(out, listener);

            // Populate a fresh (private) AST cache — never touches the shared AST_CACHE.
            ASTCache freshCache = new ASTCache();
            IAPI.IASTListener astListener = (astCtx, jfo, ast) -> {
                // jfo.toUri().getPath() gives the absolute temp-dir path,
                // matching the keys we stored in tempPathToRealUri.
                String jfoPath = jfo.toUri().getPath();
                if (tempPathToRealUri.containsKey(jfoPath)) {
                    freshCache.put(jfoPath, astCtx, (JmlCompilationUnit) ast);
                }
            };
            IAPI.setASTListener(astListener);
            List<String> args = buildArgs(modifiedSettings, "--check");
            args.addAll(filePaths);
            logInvocation("checkModifiedFilesAndGetCache", args);
            try {
                api.execute(args.toArray(new String[0]));
            } catch (Throwable t) {
                System.err.println("[CheckRunner.checkModifiedFilesAndGetCache] execute failed: " + t);
            } finally {
                IAPI.removeASTListener(astListener);
            }

            List<org.eclipse.lsp4j.Diagnostic> allDiags = new ArrayList<>();
            for (List<org.eclipse.lsp4j.Diagnostic> diags :
                    listener.toLspDiagnosticsAll(tempPathToRealUri).values()) {
                allDiags.addAll(diags);
            }
            return new CheckAndCacheResult(allDiags, freshCache, tempPathToRealUri);
        } catch (IOException e) {
            System.err.println("[CheckRunner.checkModifiedFilesAndGetCache] I/O error: " + e);
            return new CheckAndCacheResult(List.of(), new ASTCache(), Map.of());
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
            System.err.println("[CheckRunner.runEscWithSources] I/O error: " + e);
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

    // --- public API: --rac ---

    /**
     * Run {@code --rac} on a file already on disk.
     *
     * <p>Compiles the file with runtime-assertion-checking instrumentation and
     * writes the resulting {@code .class} files to the directory specified by
     * {@link OpenJMLSettings#racOutputDir} (resolved against
     * {@code workspaceFolderPaths} when relative).  The output directory is
     * created if it does not yet exist.
     *
     * @param filePath absolute path of the Java source file
     * @param uri      {@code file://} URI of the source file
     * @param settings current server settings
     * @return diagnostics and exit code (0 = success, 1 = compile errors)
     */
    public static CheckResult runRacFile(String filePath, String uri, OpenJMLSettings settings) {
        return runRacFile(filePath, uri, settings, null);
    }

    /**
     * @param outputDir optional output directory override; {@code null} means use
     *                  {@link OpenJMLSettings#racOutputDir}
     */
    public static CheckResult runRacFile(String filePath, String uri, OpenJMLSettings settings,
                                          String outputDir) {
        var listener = new LspDiagnosticListener();
        var out      = new PrintWriter(new StringWriter());
        var api      = IAPI.make(out, listener);

        List<String> args = buildArgs(settings, "--rac");

        // Resolve and create the RAC output directory.
        // Caller may supply an explicit override (e.g. the Eclipse project's bin/ folder).
        String rawDir = (outputDir != null && !outputDir.isEmpty()) ? outputDir
                : (settings.racOutputDir != null && !settings.racOutputDir.isEmpty())
                        ? settings.racOutputDir : "rac-classes";
        java.nio.file.Path outputPath;
        java.nio.file.Path raw = java.nio.file.Paths.get(rawDir);
        if (raw.isAbsolute()) {
            outputPath = raw;
        } else {
            // Resolve relative path against first workspace folder (or file's parent).
            String wsRoot = (settings.workspaceFolderPaths != null
                          && !settings.workspaceFolderPaths.isEmpty())
                    ? settings.workspaceFolderPaths.split(java.io.File.pathSeparator)[0]
                    : new java.io.File(filePath).getParent();
            outputPath = java.nio.file.Paths.get(wsRoot).resolve(raw);
        }
        try {
            java.nio.file.Files.createDirectories(outputPath);
        } catch (java.io.IOException e) {
            System.err.println("[CheckRunner.runRacFile] failed to create output dir: " + e);
        }
        args.add("-d");
        args.add(outputPath.toString());
        args.add(filePath);
        logInvocation("runRacFile", args);

        String fname = fileName(uri);
        log(ts() + " --rac " + fname + " → " + outputPath);

        int rc;
        try {
            rc = api.execute(args.toArray(new String[0]));
        } catch (Throwable e) {
            System.err.println("[CheckRunner.runRacFile] exception: " + e);
            rc = -1;
        }
        System.err.println("[CheckRunner.runRacFile] exit code " + rc);
        List<org.eclipse.lsp4j.Diagnostic> diags = listener.toLspDiagnostics(filePath, uri);
        log(ts() + " --rac " + fname + ": " + diags.size() + " diagnostic(s)");
        return new CheckResult(diags, rc, Map.of(), listener.toForeignMessages(filePath), Map.of());
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
     * If {@code javaAst.specsCompilationUnit} is non-null and different from
     * {@code javaAst}, cache the specs AST under its real URI.
     *
     * <p>This gives go-to-definition direct access to the JML specs AST so that
     * lookups from inside {@code .jml} files work without a Java-URI redirect.
     *
     * @param tempUriToRealUri maps temp-dir file URIs to real workspace URIs,
     *                         or {@code null} when no temp directory is in use
     * @param tempDirPrefix    URI prefix string of the temp directory (used to
     *                         detect and skip unmapped temp-dir paths), or {@code null}
     * @param live             if {@code true}, store in the live tier;
     *                         if {@code false}, store in the init tier
     */
    private static void cacheSpecsCu(JmlCompilationUnit javaAst, Context ctx,
                                     Map<String, String> tempUriToRealUri,
                                     String tempDirPrefix, boolean live) {
        JmlCompilationUnit specs = javaAst.specsCompilationUnit;
        if (specs == null || specs == javaAst || specs.sourcefile == null) return;
        String specsUri = specs.sourcefile.toUri().toString();
        if (tempUriToRealUri != null) {
            String real = tempUriToRealUri.get(specsUri);
            if (real != null) {
                specsUri = real;
            } else if (tempDirPrefix != null && specsUri.startsWith(tempDirPrefix)) {
                return; // in temp dir but no mapping — skip
            }
            // else: real path found via sourcepath — use directly
        }
        if (live) {
            AST_CACHE.put(specsUri, ctx, specs);
        } else {
            AST_CACHE.putInit(specsUri, ctx, specs);
        }
    }

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
        listener.setSourceContent(content);   // precompute line-start offsets for accurate columns
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

            List<String> args = buildArgs(settings, modeFlag, tempDir);
            if (methodName != null && !methodName.isEmpty()) {
                args.add("--method");
                args.add(methodName);
            }
            args.add(tempFile.toString());
            logInvocation("runOnContentWithContext", args, content);

            String fname = fileName(uri);
            String methodDesc = (methodName != null && !methodName.isEmpty()) ? " [" + methodName + "]" : "";
            if ("--check".equals(modeFlag)) log(ts() + " --check " + fname);
            else log(ts() + " --esc " + fname + methodDesc);

            // compiledPathToRealUri is populated by the AST listener — only files
            // that were actually attributed get an entry.  Start with the target.
            final Map<String, String> compiledPathToRealUri = new java.util.concurrent.ConcurrentHashMap<>();
            compiledPathToRealUri.put(tempFile.toString(), uri);
            // Pre-populate from all open files (including .jml spec files) so that
            // diagnostics from spec files are routed correctly even if the AST listener
            // does not fire for them (spec CUs are loaded differently from regular CUs).
            for (Map.Entry<String, String> e : tempUriToRealUri.entrySet()) {
                try {
                    Path p = java.nio.file.Paths.get(java.net.URI.create(e.getKey()));
                    compiledPathToRealUri.put(p.toString(), e.getValue());
                } catch (Exception ignored) {}
            }

            // Capture target AST locally so we can store with IAPI after execution.
            final String tempTargetUri = tempFile.toUri().toString();
            final JmlCompilationUnit[] capturedAst = { null };
            final com.sun.tools.javac.util.Context[] capturedCtx = { null };
            final String tempDirPrefix = tempDir.toUri().toString();
            IAPI.IASTListener astListener = (astCtx, jfo, ast) -> {
                String jfoUri = jfo.toUri().toString();
                if (jfoUri.equals(tempTargetUri)) {
                    capturedAst[0] = (JmlCompilationUnit) ast;
                    capturedCtx[0] = astCtx;
                } else {
                    String realUri = tempUriToRealUri.get(jfoUri);
                    if (realUri == null && !jfoUri.startsWith(tempDirPrefix)) {
                        // Disk file found via sourcepath (e.g. B.jml not currently open).
                        // Map it directly so its diagnostics appear as companion diagnostics.
                        realUri = jfoUri;
                    }
                    if (realUri != null) {
                        JmlCompilationUnit cu = (JmlCompilationUnit) ast;
                        AST_CACHE.put(realUri, astCtx, cu);
                        cacheSpecsCu(cu, astCtx, tempUriToRealUri, tempDirPrefix, true);
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

            // Only --check runs update the target AST cache entry; --esc discards.
            if (capturedAst[0] != null && "--check".equals(modeFlag)) {
                if (rc == 0) {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0],
                                  api, listener, tempFile.toString());
                } else {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);
                }
                cacheSpecsCu(capturedAst[0], capturedCtx[0], tempUriToRealUri, tempDirPrefix, true);
            }

            Map<String, IProverResult.Kind> proofResults =
                    prc != null ? prc.getResults() : Map.of();
            // Extract diagnostics for the target AND all files that were actually compiled.
            Map<String, List<org.eclipse.lsp4j.Diagnostic>> allDiags =
                    listener.toLspDiagnosticsAll(compiledPathToRealUri);
            List<org.eclipse.lsp4j.Diagnostic> primaryDiags =
                    allDiags.getOrDefault(uri, List.of());
            // keep uri in allDiags — allDiagnostics covers all compiled files including primary
            if ("--check".equals(modeFlag)) {
                int companionFiles  = allDiags.size() - 1;  // minus primary
                int companionTotal  = allDiags.values().stream().mapToInt(List::size).sum() - primaryDiags.size();
                String companionNote = companionFiles > 0
                        ? " (+" + companionTotal + " diagnostic(s) in " + companionFiles + " companion file(s))"
                        : "";
                log(ts() + " --check " + fname + ": " + primaryDiags.size() + " diagnostic(s)" + companionNote);
            } else {
                logEscResults(fname, proofResults, primaryDiags.size());
            }
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
        listener.setSourceContent(content);   // precompute line-start offsets for accurate columns
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

            String fname = fileName(uri);
            String methodDesc = (methodName != null && !methodName.isEmpty()) ? " [" + methodName + "]" : "";
            if ("--check".equals(modeFlag)) log(ts() + " --check " + fname);
            else log(ts() + " --esc " + fname + methodDesc);

            // Capture AST in local vars so we can store with IAPI after execution.
            final String tempUriStr = tempFile.toUri().toString();
            final JmlCompilationUnit[] capturedAst = { null };
            final com.sun.tools.javac.util.Context[] capturedCtx = { null };
            IAPI.IASTListener astListener = (ctx, jfo, ast) -> {
                if (jfo.toUri().toString().equals(tempUriStr)) {
                    capturedAst[0] = (JmlCompilationUnit) ast;
                    capturedCtx[0] = ctx;
                }
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

            // Only --check runs update the AST cache.  --esc runs do not redo attribution;
            // any AST they happen to produce is discarded to preserve the --check entry
            // (and its stored IAPI for the doESC API path).
            if (capturedAst[0] != null && "--check".equals(modeFlag)) {
                if (rc == 0) {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0],
                                  api, listener, tempFile.toString());
                } else {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);  // failed check: basic entry
                }
                cacheSpecsCu(capturedAst[0], capturedCtx[0], null, null, true);
            }

            Map<String, IProverResult.Kind> proofResults =
                    prc != null ? prc.getResults() : Map.of();
            List<org.eclipse.lsp4j.Diagnostic> diags =
                    listener.toLspDiagnostics(tempFile.toString(), uri);
            if ("--check".equals(modeFlag))
                log(ts() + " --check " + fname + ": " + diags.size() + " diagnostic(s)");
            else
                logEscResults(fname, proofResults, diags.size());
            return new CheckResult(diags, rc,
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

        String fname = fileName(uri);
        String methodDesc = (methodName != null && !methodName.isEmpty()) ? " [" + methodName + "]" : "";
        if ("--check".equals(modeFlag)) log(ts() + " --check " + fname);
        else log(ts() + " --esc " + fname + methodDesc);

        // Capture the primary file's AST locally; store with IAPI on successful --check.
        final String fileUriStr = new java.io.File(filePath).toURI().toString();
        final JmlCompilationUnit[] capturedAst = { null };
        final com.sun.tools.javac.util.Context[] capturedCtx = { null };
        IAPI.IASTListener astListener = (ctx, jfo, ast) -> {
            String jfoUri = jfo.toUri().toString();
            if (jfoUri.equals(fileUriStr)) {
                capturedAst[0] = (JmlCompilationUnit) ast;
                capturedCtx[0] = ctx;
            } else {
                // Additional files pulled in via -sourcepath: store basic entry.
                JmlCompilationUnit cu = (JmlCompilationUnit) ast;
                AST_CACHE.put(jfoUri, ctx, cu);
                cacheSpecsCu(cu, ctx, null, null, true);
            }
        };
        IAPI.setASTListener(astListener);
        int rc;
        try {
            rc = api.execute(args.toArray(new String[0]));
        } finally {
            IAPI.removeASTListener(astListener);
        }
        System.err.println("[CheckRunner.runOnFile] exit code " + rc
                + " (" + modeFlag + ")");

        // Only --check runs update the AST cache; --esc discards to preserve the --check entry.
        if (capturedAst[0] != null && "--check".equals(modeFlag)) {
            if (rc == 0) {
                AST_CACHE.put(uri, capturedCtx[0], capturedAst[0],
                              api, listener, filePath);
            } else {
                AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);
            }
            cacheSpecsCu(capturedAst[0], capturedCtx[0], null, null, true);
        }

        Map<String, IProverResult.Kind> proofResults =
                prc != null ? prc.getResults() : Map.of();
        List<org.eclipse.lsp4j.Diagnostic> diags = listener.toLspDiagnostics(filePath, uri);
        if ("--check".equals(modeFlag))
            log(ts() + " --check " + fname + ": " + diags.size() + " diagnostic(s)");
        else
            logEscResults(fname, proofResults, diags.size());
        return new CheckResult(diags, rc,
                proofResults, listener.toForeignMessages(filePath), Map.of());
    }

    /**
     * Run {@code --check} on a single file, populating the init-tier AST cache.
     *
     * <p>Used by the background workspace index to check files one at a time so
     * diagnostics can be published incrementally and the indexing thread does not
     * monopolise the executor pool.  The {@code isIndexing()} flag is managed by
     * the caller.
     *
     * @param filePath absolute path of the {@code .java} file to check
     * @param uri      LSP document URI for the file
     * @param settings current OpenJML settings
     * @return diagnostics produced by the check (caller decides whether to publish)
     */
    public static List<org.eclipse.lsp4j.Diagnostic> indexOneFile(
            String filePath, String uri, OpenJMLSettings settings) {
        var out      = new PrintWriter(new StringWriter());
        var listener = new LspDiagnosticListener();
        var api      = IAPI.make(out, listener);

        List<String> args = buildArgs(settings, "--check");
        args.add(filePath);

        IAPI.IASTListener astListener = (ctx, jfo, ast) -> {
            JmlCompilationUnit cu = (JmlCompilationUnit) ast;
            AST_CACHE.putInit(jfo.toUri().toString(), ctx, cu);
            cacheSpecsCu(cu, ctx, null, null, false);
        };
        IAPI.setASTListener(astListener);
        try {
            api.execute(args.toArray(new String[0]));
        } catch (Throwable e) {
            System.err.println("[CheckRunner.indexOneFile] " + filePath + ": " + e);
        } finally {
            IAPI.removeASTListener(astListener);
        }
        return listener.toLspDiagnostics(filePath, uri);
    }

    // --- public API: in-process doESC via cached IAPI ---

    /**
     * Run ESC on a single method using the IAPI instance from the last successful
     * {@code --check} run for {@code uri}.
     *
     * <p>Falls back to the subprocess {@code --esc --method} path when:
     * <ul>
     *   <li>No cache entry exists yet (file not yet checked), or</li>
     *   <li>The last check had errors ({@link ASTCache.Entry#supportsDoEsc()} is false), or</li>
     *   <li>The method name is not found in the cached AST.</li>
     * </ul>
     *
     * <p>Concurrent doESC calls on the same or different URIs proceed in parallel;
     * {@link IAPI#doESC} is thread-safe.  Only {@code setProofResultListener} is
     * briefly synchronized on the {@code api} object.
     *
     * @param uri        LSP document URI (used for cache lookup and diagnostic mapping)
     * @param methodName fully-qualified or simple method name
     */
    public static CheckResult runDoEscMethod(String uri, String methodName,
                                              OpenJMLSettings settings) {
        ASTCache.Entry entry = AST_CACHE.get(uri);
        if (entry == null || !entry.supportsDoEsc()) {
            System.err.println("[CheckRunner.runDoEscMethod] no cached IAPI for " + uri
                    + " — falling back to subprocess");
            String filePath = uriToPath(uri);
            if (filePath != null) return runEscFileMethod(filePath, uri, methodName, settings);
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of());
        }

        String simple = simpleName(methodName);
        List<JmlTree.JmlMethodDecl> methods = findMethodsBySimpleName(entry.ast(), simple);
        if (methods.isEmpty()) {
            System.err.println("[CheckRunner.runDoEscMethod] method '" + simple
                    + "' not found in cached AST for " + uri + " — falling back to subprocess");
            String filePath = uriToPath(uri);
            if (filePath != null) return runEscFileMethod(filePath, uri, methodName, settings);
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of());
        }

        List<org.eclipse.lsp4j.Diagnostic> allDiags = new ArrayList<>();
        Map<String, IProverResult.Kind> proofResults = new LinkedHashMap<>();
        int exitCode = 0;
        for (JmlTree.JmlMethodDecl method : methods) {
            SingleEscResult r = doEscOneMethod(uri, method, entry);
            if (r.kind() != null) proofResults.put(r.name(), r.kind());
            allDiags.addAll(r.diags());
            if (r.exitCode() != 0) exitCode = r.exitCode();
        }
        return new CheckResult(allDiags, exitCode, proofResults, List.of(), Map.of());
    }

    /** Holds the result of a single-method doESC call. */
    public record MethodEscResult(String name, IProverResult.Kind kind,
                                   List<org.eclipse.lsp4j.Diagnostic> diags, int exitCode) {}

    /**
     * Run ESC on all methods in the file for {@code uri} using the cached IAPI.
     *
     * <p>Builds a work list of all methods, submits them to {@link OpenJMLSettings#escPool}
     * (N concurrent, where N = pool size = {@code escThreads}), and fires
     * {@code onMethodComplete} on the calling thread as each method finishes.
     * Returns a {@link CompletableFuture} that completes with the merged
     * {@link CheckResult} after all methods are done.
     *
     * <p>Falls back to a subprocess {@code --esc} run (synchronous, wrapped in a
     * completed future) when no cached IAPI is available.
     *
     * @param onMethodComplete called on the pool thread as each method finishes;
     *                         may be {@code null} if no per-method callback is needed
     */
    public static CompletableFuture<CheckResult> runDoEscFileAsync(
            String uri, OpenJMLSettings settings,
            Consumer<MethodEscResult> onMethodComplete) {
        ASTCache.Entry entry = AST_CACHE.get(uri);
        if (entry == null || !entry.supportsDoEsc()) {
            System.err.println("[CheckRunner.runDoEscFileAsync] no cached IAPI for " + uri
                    + " — falling back to subprocess");
            String filePath = uriToPath(uri);
            CheckResult result = (filePath != null)
                    ? runEscFile(filePath, uri, settings)
                    : new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of());
            return CompletableFuture.completedFuture(result);
        }

        List<JmlTree.JmlMethodDecl> methods = findAllMethods(entry.ast());
        if (methods.isEmpty()) {
            return CompletableFuture.completedFuture(
                    new CheckResult(List.of(), 0, Map.of(), List.of(), Map.of()));
        }

        // Submit each method to the pool; fire the callback as each completes.
        List<CompletableFuture<MethodEscResult>> futures = new ArrayList<>(methods.size());
        for (JmlTree.JmlMethodDecl method : methods) {
            CompletableFuture<MethodEscResult> f = CompletableFuture
                    .supplyAsync(() -> {
                        var r = doEscOneMethod(uri, method, entry);
                        return new MethodEscResult(r.name(), r.kind(), r.diags(), r.exitCode());
                    }, settings.escPool)
                    .whenComplete((r, ex) -> {
                        if (r != null && onMethodComplete != null) onMethodComplete.accept(r);
                        if (ex != null) System.err.println(
                                "[CheckRunner.runDoEscFileAsync] task failed: " + ex);
                    });
            futures.add(f);
        }

        // Merge all results into a single CheckResult when all methods are done.
        return CompletableFuture.allOf(futures.toArray(new CompletableFuture[0]))
                .thenApply(v -> {
                    List<org.eclipse.lsp4j.Diagnostic> allDiags = new ArrayList<>();
                    Map<String, IProverResult.Kind> proofResults = new LinkedHashMap<>();
                    int exitCode = 0;
                    for (CompletableFuture<MethodEscResult> f : futures) {
                        MethodEscResult r = f.getNow(null);
                        if (r == null) continue;
                        if (r.kind() != null) proofResults.put(r.name(), r.kind());
                        allDiags.addAll(r.diags());
                        if (r.exitCode() != 0) exitCode = r.exitCode();
                    }
                    System.err.println("[CheckRunner.runDoEscFileAsync] done, exitCode="
                            + exitCode + " diags=" + allDiags.size() + " uri=" + uri);
                    return new CheckResult(allDiags, exitCode, proofResults, List.of(), Map.of());
                });
    }

    /** Blocking wrapper around {@link #runDoEscFileAsync} (used by tests). */
    public static CheckResult runDoEscFile(String uri, OpenJMLSettings settings) {
        try {
            return runDoEscFileAsync(uri, settings, null).get();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of());
        } catch (ExecutionException e) {
            System.err.println("[CheckRunner.runDoEscFile] failed: " + e.getCause());
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of());
        }
    }

    /** Holds the result of a single-method doESC call (internal alias for MethodEscResult). */
    private record SingleEscResult(String name, IProverResult.Kind kind,
                                    List<org.eclipse.lsp4j.Diagnostic> diags, int exitCode) {}

    /**
     * Run doESC on one method.
     *
     * <p>{@link IAPI#doESC} is NOT thread-safe on the same IAPI instance; calls for
     * the same entry are serialized via the entry's {@code escLock}.  Methods from
     * different files (different IAPI instances, different locks) proceed in parallel.
     * The lock is held only for the duration of the single-method call, so all methods
     * of a file are queued individually — each releases the lock as soon as it finishes,
     * allowing the next queued method to start while results are being processed.
     *
     * <p>Diagnostic capture uses a {@link ThreadLocal} in {@link LspDiagnosticListener}
     * and is safe to start/stop outside the lock.
     */
    private static SingleEscResult doEscOneMethod(String uri,
                                                   JmlTree.JmlMethodDecl method,
                                                   ASTCache.Entry entry) {
        String msig = method.sym != null
                ? method.sym.owner.toString() + " " + method.sym.toString()
                : method.name.toString();
        System.err.println("[CheckRunner.doEscOneMethod] doESC on " + method.name + " in " + uri);
        log(ts() + " --esc " + msig + " starting");
        entry.diagListener().startCapture();
        IProverResult result;
        entry.escLock().lock();
        try {
            result = entry.api().doESC(method);
        } finally {
            entry.escLock().unlock();
        }
        var rawDiags = entry.diagListener().stopCapture();

        List<org.eclipse.lsp4j.Diagnostic> lspDiags =
                LspDiagnosticListener.toLspDiagnosticsFromList(
                        rawDiags, entry.sourcePath(), uri);
        IProverResult.Kind kind = result != null ? result.result() : null;
        int exitCode = (kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT) ? 6 : 0;
        System.err.println("[CheckRunner.doEscOneMethod] " + method.name
                + " -> " + kind + ", exitCode=" + exitCode);
        log(ts() + " --esc " + msig + ": " + kindLabel(kind));
        return new SingleEscResult(method.name.toString(), kind, lspDiags, exitCode);
    }

    // --- AST method-scanning helpers ---

    /** Extract the simple (unqualified) method name from a possibly-qualified name. */
    private static String simpleName(String fqn) {
        int dot = fqn.lastIndexOf('.');
        return dot >= 0 ? fqn.substring(dot + 1) : fqn;
    }

    /** Find all non-synthetic methods with the given simple name in the AST. */
    private static List<JmlTree.JmlMethodDecl> findMethodsBySimpleName(
            JmlCompilationUnit ast, String simpleName) {
        List<JmlTree.JmlMethodDecl> result = new ArrayList<>();
        new JmlTreeScanner(null) {
            @Override
            public void visitMethodDef(JCTree.JCMethodDecl tree) {
                if (tree instanceof JmlTree.JmlMethodDecl md
                        && simpleName.equals(tree.name.toString())) {
                    result.add(md);
                }
                // do NOT recurse into the method body (no local classes)
            }
            @Override public void visitBlock(JCTree.JCBlock b) { /* skip */ }
        }.scan(ast);
        return result;
    }

    /** Find all non-synthetic methods (excluding {@code <clinit>}) in the AST. */
    private static List<JmlTree.JmlMethodDecl> findAllMethods(JmlCompilationUnit ast) {
        List<JmlTree.JmlMethodDecl> result = new ArrayList<>();
        new JmlTreeScanner(null) {
            @Override
            public void visitMethodDef(JCTree.JCMethodDecl tree) {
                if (tree instanceof JmlTree.JmlMethodDecl md) {
                    String name = tree.name.toString();
                    if (!"<clinit>".equals(name)) result.add(md);  // include constructors
                }
                // do NOT recurse into the method body (no local classes)
            }
            @Override public void visitBlock(JCTree.JCBlock b) { /* skip */ }
        }.scan(ast);
        return result;
    }

    /**
     * When {@code true} (default), Tab-2 tool options from the Eclipse plugin
     * are read from a generated {@code .properties} file
     * ({@link OpenJMLSettings#generatedPropertiesFile}).
     * When {@code false}, they arrive as a flat args list
     * ({@link OpenJMLSettings#toolArgs}).
     *
     * <p>Must match the {@code USE_PROPERTIES_FILE} flag in the Eclipse plugin's
     * {@code OpenJMLOptions}.
     */
    private static final boolean USE_PROPERTIES_FILE = true;

    private static List<String> buildArgs(OpenJMLSettings settings, String modeFlag) {
        return buildArgs(settings, modeFlag, null);
    }

    private static List<String> buildArgs(OpenJMLSettings settings, String modeFlag, Path prefixDir) {
        List<String> args = new ArrayList<>();

        if (USE_PROPERTIES_FILE) {
            // Generated Eclipse-preferences file — lowest priority, before user file.
            if (settings.generatedPropertiesFile != null
                    && !settings.generatedPropertiesFile.isEmpty()) {
                args.add("--properties");
                args.add(settings.generatedPropertiesFile);
            }
        } else {
            // Command-line args mode: prepend tool args before the mode flag.
            if (settings.toolArgs != null && !settings.toolArgs.isEmpty()) {
                args.addAll(settings.toolArgs);
            }
        }

        // User's workspace properties file overrides the generated file above.
        if (settings.propertiesFile != null && !settings.propertiesFile.isEmpty()) {
            args.add("--properties");
            args.add(settings.propertiesFile);
        }
        args.add(modeFlag);
        if (settings.specsPath != null && !settings.specsPath.isEmpty()) {
            args.add("--specs-path");
            args.add(settings.specsPath);
        }
        if (settings.solversPath != null && !settings.solversPath.isEmpty()) {
            args.add("--solvers-path");
            args.add(settings.solversPath);
        }
        String sp = buildEffectiveSourcePath(prefixDir, settings);
        if (!sp.isEmpty()) {
            args.add("-sourcepath");
            args.add(sp);
        }
        if (settings.classPath != null && !settings.classPath.isEmpty()) {
            args.add("-classpath");
            args.add(settings.classPath);
        }
        return args;
    }

    /**
     * Build the effective {@code -sourcepath} value.
     *
     * <p>Concatenates (path-separator-separated, omitting empty parts):
     * <ol>
     *   <li>{@code prefixDir} — temp directory holding in-memory file contents
     *       (may be {@code null} when there is no temp dir, e.g. for on-disk checks)</li>
     *   <li>{@link OpenJMLSettings#workspaceFolderPaths} — workspace folders
     *       reported by the editor at {@code initialize} time</li>
     *   <li>{@link OpenJMLSettings#sourcePath} — explicit user setting, if non-empty</li>
     *   <li>{@link OpenJMLSettings#classPath} — only appended when
     *       {@link OpenJMLSettings#sourcePath} is absent, so compiled dependencies
     *       can serve as a source fallback when no explicit source root is configured</li>
     * </ol>
     */
    static String buildEffectiveSourcePath(Path prefixDir, OpenJMLSettings settings) {
        List<String> parts = new ArrayList<>();
        if (prefixDir != null) parts.add(prefixDir.toString());
        if (settings.workspaceFolderPaths != null && !settings.workspaceFolderPaths.isEmpty())
            parts.add(settings.workspaceFolderPaths);
        boolean hasSourcePath = settings.sourcePath != null && !settings.sourcePath.isEmpty();
        if (hasSourcePath) {
            parts.add(settings.sourcePath);
        } else if (settings.classPath != null && !settings.classPath.isEmpty()) {
            parts.add(settings.classPath);
        }
        return String.join(java.io.File.pathSeparator, parts);
    }

    /**
     * Build the effective specs path for a run that uses a temp directory.
     *
     * <p>If the user has not specified a specs path, return {@code ""} so that
     * no {@code --specs-path} argument is forwarded to OpenJML; it will then
     * fall back to the source path (which already includes {@code prefixDir}).
     *
     * <p>If the user has specified a specs path, prepend {@code prefixDir} and
     * workspace folder paths so that dirty {@code .jml} files in the temp dir
     * take priority over on-disk versions, matching the sourcepath logic.
     */
    static String buildEffectiveSpecsPath(Path prefixDir, OpenJMLSettings settings) {
        if (settings.specsPath == null || settings.specsPath.isEmpty()) return "";
        List<String> parts = new ArrayList<>();
        if (prefixDir != null) parts.add(prefixDir.toString());
        if (settings.workspaceFolderPaths != null && !settings.workspaceFolderPaths.isEmpty())
            parts.add(settings.workspaceFolderPaths);
        parts.add(settings.specsPath);
        return String.join(java.io.File.pathSeparator, parts);
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
        if (!name.endsWith(".java") && !name.endsWith(".jml"))
            name = name.replaceAll("[^A-Za-z0-9_]", "_") + ".java";
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
