package org.openjml.lsp;

import org.openjml.IAPI;
import org.openjml.MockJavaFileObject;
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
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Supplier;

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
     * When {@code true} (default), dirty {@code .java} files in the snapshot are
     * served as in-memory {@link MockJavaFileObject} instances — no temporary files
     * are written to disk for them.  Set to {@code false} to fall back to the
     * original temp-file behaviour for regression testing or debugging.
     */
    public static boolean useMockFiles = true;

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

    static void log(String msg) {
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
    /** Formats the per-run cancellation summary for the console log. */
    private static String cancelSummary(Map<String, IProverResult.Kind> proofResults) {
        long completed = proofResults.values().stream()
                .filter(k -> k != IProverResult.CANCELLED).count();
        boolean hasCancelled = proofResults.containsValue(IProverResult.CANCELLED);
        return completed + " method(s) completed before cancel"
                + (hasCancelled ? ", 1 cancelled" : "");
    }

    private static String kindLabel(IProverResult.Kind kind) {
        if (kind == null)                                                      return "unknown";
        if (kind == IProverResult.UNSAT)                                       return "Verified";
        if (kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT)   return "Not Verified";
        if (kind == IProverResult.CANCELLED)                                   return "Cancelled";
        if (kind == IProverResult.TIMEOUT)                                     return "Timeout";
        if (kind == IProverResult.SKIPPED)                                     return "Skipped";
        return kind.toString();
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
        /** Returns {@code true} when OpenJML reported a catastrophic error (exit codes 3 and 4
         *  are not distinguished — both indicate resource exhaustion, misconfiguration, or
         *  an internal bug). */
        public boolean isInternalError() { return exitCode == 3 || exitCode == 4; }
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

        /**
         * Optional callback invoked after each final proof result is recorded.
         * Receives the {@link MethodSymbol} so the caller can publish per-file
         * diagnostics immediately rather than waiting for the full run to finish.
         */
        private final java.util.function.Consumer<MethodSymbol> perMethodCallback;

        ProofResultCollector() { this(null); }

        ProofResultCollector(java.util.function.Consumer<MethodSymbol> perMethodCallback) {
            this.perMethodCallback = perMethodCallback;
        }

        @Override
        public void reportProofResult(MethodSymbol msym, IProverResult result) {
            IProverResult.Kind kind = result.result();
            // Ignore transient lifecycle notifications; record all terminal outcomes
            // (including CANCELLED — the method that was mid-proof when cancel fired).
            if (kind == IProverResult.RUNNING || kind == IProverResult.COMPLETED) {
                return;
            }
            String name = msym.getSimpleName().toString();
            results.put(name, kind);
            // Log immediately so the console shows progress as each method completes.
            javax.tools.JavaFileObject src =
                    msym.enclClass() != null ? msym.enclClass().sourcefile : null;
            String fname = src != null ? fileName(src.getName()) : "unknown";
            log(ts() + " --esc " + fname + " " + name + ": " + kindLabel(kind));
            if (perMethodCallback != null) perMethodCallback.accept(msym);
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
        // Clear nav-cache entries for files under these roots, then populate
        // fresh entries via the AST listener so workspace/symbol can find them.
        AST_CACHE.clearNavForRoots(paths);
        IAPI.IASTListener astListener = (ctx, jfo, ast) -> {
            String uri = jfo.toUri().normalize().toString();
            AST_CACHE.putNav(uri, ctx, (JmlCompilationUnit) ast, paths);
        };
        api.setASTListener(astListener);
        int rc;
        try {
            rc = api.execute(args.toArray(new String[0]));
        } finally {
            api.removeASTListener(astListener);
        }
        System.err.println("[CheckRunner.runCheckDir] exit code " + rc
                + " for " + paths.size() + " path(s)");
        return new DirCheckResult(listener.toLspDiagnosticsByFile(), rc, Map.of());
    }

    /**
     * Run {@code --check} on one or more files/directories, substituting dirty
     * in-memory files from {@code snapshot} for their on-disk counterparts.
     *
     * <p>When {@link #useMockFiles} is {@code true} (default), dirty {@code .java}
     * files are served as in-memory {@link MockJavaFileObject} instances — no
     * temporary files are created for them.  Dirty {@code .jml} files still use
     * a temp directory for now.
     *
     * <p>Fast path: when {@code snapshot} is empty, delegates to
     * {@link #runCheckDir(List, OpenJMLSettings)}.
     */
    public static DirCheckResult runCheckDirWithContext(
            List<String> paths, Map<String, String> snapshot, OpenJMLSettings settings) {
        if (snapshot.isEmpty()) return runCheckDir(paths, settings);
        if (!useMockFiles) return runCheckDirWithContextLegacy(paths, snapshot, settings);

        Map<String, String> allPathToRealUri = new java.util.LinkedHashMap<>();
        org.openjml.MockFiles mockFiles = new org.openjml.MockFiles();

        // Dirty files → MockJavaFileObject registered by URI.
        // .java: file-manager interception via MockAwareFileManager.
        // .jml:  specs-path interception via JmlSpecs.withMockOverride.
        for (Map.Entry<String, String> e : snapshot.entrySet()) {
            String uri     = e.getKey();
            String content = e.getValue();
            java.net.URI fileUri = java.net.URI.create(uri);
            MockJavaFileObject jfo = new MockJavaFileObject(fileUri, content);
            mockFiles.addMockByUri(fileUri.normalize(), jfo);
            allPathToRealUri.put(jfo.getName(), uri);
        }

        // Walk requested paths: add .java files to the explicit arg list.
        List<String> fileList = new ArrayList<>();
        for (String path : paths) {
            java.nio.file.Path p = java.nio.file.Path.of(path);
            if (Files.isDirectory(p)) {
                try (var stream = Files.walk(p)) {
                    stream.filter(f -> { String s = f.toString(); return s.endsWith(".java") || s.endsWith(".jml"); })
                          .forEach(f -> {
                              String diskPath = f.toString();
                              String diskUri  = f.toUri().toString();
                              if (diskPath.endsWith(".java")) {
                                  fileList.add(diskPath);
                                  allPathToRealUri.put(diskPath, diskUri);
                              } else {
                                  allPathToRealUri.put(diskPath, diskUri); // .jml: diagnostic routing only
                              }
                          });
                } catch (IOException ex) {
                    System.err.println("[CheckRunner.runCheckDirWithContext] walk failed for " + path + ": " + ex);
                }
            } else {
                String diskUri = p.toUri().toString();
                if (path.endsWith(".jml")) {
                    allPathToRealUri.put(path, diskUri);
                } else {
                    fileList.add(path);
                    allPathToRealUri.put(path, diskUri);
                }
            }
        }

        if (fileList.isEmpty()) return new DirCheckResult(Map.of(), 0, Map.of());

        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);
        List<String> args = buildArgs(settings, "--check");
        args.addAll(fileList);
        logInvocation("runCheckDirWithContext", args);
        Map<String, String> normToReal = new java.util.HashMap<>();
        for (Map.Entry<String, String> e : snapshot.entrySet()) {
            try { normToReal.put(java.net.URI.create(e.getKey()).normalize().toString(), e.getKey()); }
            catch (Exception ignored) {}
        }
        AST_CACHE.clearNavForRoots(paths);
        IAPI.IASTListener astListener = (astCtx, jfo, ast) -> {
            String jfoUri = jfo.toUri().normalize().toString();
            String realUri = normToReal.getOrDefault(jfoUri, jfoUri);
            try {
                String astSrcUri = ((org.jmlspecs.openjml.JmlTree.JmlCompilationUnit) ast)
                        .sourcefile.toUri().normalize().toString();
                System.err.println("[AST listener] jfo=" + jfoUri
                        + (jfoUri.equals(astSrcUri) ? "" : " ast.sourcefile=" + astSrcUri));
            } catch (Exception ignored) {}
            AST_CACHE.putNav(realUri, astCtx,
                    (org.jmlspecs.openjml.JmlTree.JmlCompilationUnit) ast, paths);
        };
        api.setASTListener(astListener);
        int rc;
        try {
            rc = api.execute(args.toArray(new String[0]), mockFiles);
        } finally {
            api.removeASTListener(astListener);
        }
        System.err.println("[CheckRunner.runCheckDirWithContext] exit code " + rc
                + " for " + fileList.size() + " file(s)");
        return new DirCheckResult(listener.toLspDiagnosticsAll(allPathToRealUri), rc, Map.of());
    }

    /** Legacy temp-file implementation of {@link #runCheckDirWithContext}, used when
     *  {@link #useMockFiles} is {@code false}. */
    private static DirCheckResult runCheckDirWithContextLegacy(
            List<String> paths, Map<String, String> snapshot, OpenJMLSettings settings) {
        Path tempDir = null;
        try {
            tempDir = Files.createTempDirectory("openjml-lsp-check-");

            Map<String, String> uriToTempPath  = new java.util.HashMap<>();
            Map<String, String> allPathToRealUri = new java.util.LinkedHashMap<>();
            for (Map.Entry<String, String> e : snapshot.entrySet()) {
                String uri     = e.getKey();
                String content = e.getValue();
                try {
                    Path tempFile = writeToTempDir(tempDir, uri, content);
                    uriToTempPath.put(uri, tempFile.toString());
                    allPathToRealUri.put(tempFile.toString(), uri);
                } catch (IOException ex) {
                    System.err.println("[CheckRunner.runCheckDirWithContextLegacy] write failed for " + uri + ": " + ex);
                }
            }

            List<String> fileList = new ArrayList<>();
            for (String path : paths) {
                java.nio.file.Path p = java.nio.file.Path.of(path);
                if (Files.isDirectory(p)) {
                    try (var stream = Files.walk(p)) {
                        stream.filter(f -> { String s = f.toString(); return s.endsWith(".java") || s.endsWith(".jml"); })
                              .forEach(f -> {
                                  String diskPath = f.toString();
                                  String diskUri  = f.toUri().toString();
                                  String tempPath = uriToTempPath.get(diskUri);
                                  if (diskPath.endsWith(".java")) {
                                      if (tempPath != null) fileList.add(tempPath);
                                      else { fileList.add(diskPath); allPathToRealUri.put(diskPath, diskUri); }
                                  } else {
                                      if (tempPath == null) allPathToRealUri.put(diskPath, diskUri);
                                  }
                              });
                    } catch (IOException ex) {
                        System.err.println("[CheckRunner.runCheckDirWithContextLegacy] walk failed for " + path + ": " + ex);
                    }
                } else {
                    String diskUri  = p.toUri().toString();
                    String tempPath = uriToTempPath.get(diskUri);
                    if (path.endsWith(".jml")) {
                        if (tempPath == null) allPathToRealUri.put(path, diskUri);
                    } else {
                        if (tempPath != null) fileList.add(tempPath);
                        else { fileList.add(path); allPathToRealUri.put(path, diskUri); }
                    }
                }
            }

            if (fileList.isEmpty()) return new DirCheckResult(Map.of(), 0, Map.of());

            var listener = new LspDiagnosticListener();
            var out = new PrintWriter(new StringWriter());
            var api = IAPI.make(out, listener);
            List<String> args = buildArgs(settings, "--check", tempDir);
            args.addAll(fileList);
            logInvocation("runCheckDirWithContextLegacy", args);
            int rc = api.execute(args.toArray(new String[0]));
            System.err.println("[CheckRunner.runCheckDirWithContextLegacy] exit code " + rc
                    + " for " + fileList.size() + " file(s)");
            return new DirCheckResult(listener.toLspDiagnosticsAll(allPathToRealUri), rc, Map.of());
        } catch (IOException e) {
            System.err.println("[CheckRunner.runCheckDirWithContextLegacy] I/O error: " + e);
            return runCheckDir(paths, settings);
        } finally {
            deleteTempDir(tempDir);
        }
    }

    /**
     * Callback invoked after each method's proof completes during an ESC run.
     * Receives the file URI, the diagnostics accumulated so far for that file,
     * and a snapshot of the proof results recorded so far (all methods that have
     * finished, keyed by simple method name).  Use the snapshot to update
     * per-method code-lens status incrementally without waiting for the full run.
     */
    @FunctionalInterface
    public interface EscProgressCallback {
        void accept(String uri,
                    List<org.eclipse.lsp4j.Diagnostic> diagsSoFar,
                    Map<String, IProverResult.Kind> proofResultsSoFar);
    }

    /**
     * Run {@code --esc --dirs path1 path2 ...}.
     *
     * @param perFileCallback  called after each method's proof completes with the
     *                         file URI, the diagnostics accumulated so far for that
     *                         file, and a snapshot of proof results so far.
     *                         Lets the caller update code-lens status and publish
     *                         markers progressively.  Pass {@code null} to skip.
     */
    public static DirCheckResult runEscDir(List<String> paths, OpenJMLSettings settings,
            EscProgressCallback perFileCallback) {
        return runEscDir(paths, settings, perFileCallback, null);
    }

    static DirCheckResult runEscDir(List<String> paths, OpenJMLSettings settings,
            EscProgressCallback perFileCallback, Consumer<IAPI> onApiReady) {
        var listener = new LspDiagnosticListener();
        listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);
        ProofResultCollector[] prcRef = {null};
        prcRef[0] = new ProofResultCollector(perFileCallback == null ? null : msym -> {
            javax.tools.JavaFileObject src =
                    msym.enclClass() != null ? msym.enclClass().sourcefile : null;
            if (src == null) { log("[runEscDir callback] src is null for " + msym); return; }
            String uri;
            try { uri = java.nio.file.Path.of(src.getName()).toUri().toString(); }
            catch (Exception e) { log("[runEscDir callback] URI conversion failed: " + e); return; }
            List<org.eclipse.lsp4j.Diagnostic> diags = listener.getLspDiagnosticsForUri(uri);
            perFileCallback.accept(uri, diags, Map.copyOf(prcRef[0].getResults()));
        });
        ProofResultCollector prc = prcRef[0];
        api.setProofResultListener(prc);
        if (onApiReady != null) onApiReady.accept(api);

        List<String> args = buildArgs(settings, "--esc");
        args.add("--dirs");
        args.addAll(paths);
        logInvocation("runEscDir", args);
        log(ts() + " --esc --dirs " + paths + invocationSuffix(args));
        int rc = api.execute(args.toArray(new String[0]));
        Map<String, List<org.eclipse.lsp4j.Diagnostic>> diagsByUri = listener.toLspDiagnosticsByFile();
        Map<String, IProverResult.Kind> proofResults = prc.getResults();
        int totalDiags = diagsByUri.values().stream().mapToInt(List::size).sum();
        if (rc == 5)
            log(ts() + " --esc cancelled: " + cancelSummary(proofResults) + ", " + totalDiags + " diagnostic(s)");
        else
            log(ts() + " --esc complete: " + proofResults.size() + " method(s), " + totalDiags + " diagnostic(s)");
        return new DirCheckResult(diagsByUri, rc, proofResults);
    }

    /** Convenience overload with no progressive callback. */
    public static DirCheckResult runEscDir(List<String> paths, OpenJMLSettings settings) {
        return runEscDir(paths, settings, null);
    }

    /**
     * Run {@code --esc} on one or more files/directories, substituting dirty
     * in-memory files from {@code snapshot} for their on-disk counterparts.
     *
     * <p>When {@link #useMockFiles} is {@code true} (default), dirty {@code .java}
     * files are served as in-memory {@link MockJavaFileObject} instances.
     * The {@code perFileCallback} receives the <em>real</em> URI so callers can
     * publish progressive diagnostics without remapping.
     *
     * <p>Fast path: when {@code snapshot} is empty, delegates to
     * {@link #runEscDir(List, OpenJMLSettings, EscProgressCallback)}.
     */
    public static DirCheckResult runEscDirWithContext(
            List<String> paths, Map<String, String> snapshot, OpenJMLSettings settings,
            EscProgressCallback perFileCallback) {
        return runEscDirWithContext(paths, snapshot, settings, perFileCallback, null);
    }

    static DirCheckResult runEscDirWithContext(
            List<String> paths, Map<String, String> snapshot, OpenJMLSettings settings,
            EscProgressCallback perFileCallback, Consumer<IAPI> onApiReady) {
        if (snapshot.isEmpty()) return runEscDir(paths, settings, perFileCallback, onApiReady);
        if (!useMockFiles) return runEscDirWithContextLegacy(paths, snapshot, settings, perFileCallback, onApiReady);

        Map<String, String> allPathToRealUri = new java.util.LinkedHashMap<>();
        org.openjml.MockFiles mockFiles = new org.openjml.MockFiles();

        // Dirty files → MockJavaFileObject registered by URI.
        // .java: file-manager interception via MockAwareFileManager.
        // .jml:  specs-path interception via JmlSpecs.withMockOverride.
        for (Map.Entry<String, String> e : snapshot.entrySet()) {
            String uri     = e.getKey();
            String content = e.getValue();
            java.net.URI fileUri = java.net.URI.create(uri);
            MockJavaFileObject jfo = new MockJavaFileObject(fileUri, content);
            mockFiles.addMockByUri(fileUri.normalize(), jfo);
            allPathToRealUri.put(jfo.getName(), uri);
        }

        List<String> fileList = new ArrayList<>();
        for (String path : paths) {
            java.nio.file.Path p = java.nio.file.Path.of(path);
            if (Files.isDirectory(p)) {
                try (var stream = Files.walk(p)) {
                    stream.filter(f -> { String s = f.toString(); return s.endsWith(".java") || s.endsWith(".jml"); })
                          .forEach(f -> {
                              String diskPath = f.toString();
                              String diskUri  = f.toUri().toString();
                              if (diskPath.endsWith(".java")) {
                                  fileList.add(diskPath);
                                  allPathToRealUri.put(diskPath, diskUri);
                              } else {
                                  allPathToRealUri.put(diskPath, diskUri);
                              }
                          });
                } catch (IOException ex) {
                    System.err.println("[CheckRunner.runEscDirWithContext] walk failed for " + path + ": " + ex);
                }
            } else {
                String diskUri = p.toUri().toString();
                if (path.endsWith(".jml")) allPathToRealUri.put(path, diskUri);
                else { fileList.add(path); allPathToRealUri.put(path, diskUri); }
            }
        }

        if (fileList.isEmpty()) return new DirCheckResult(Map.of(), 0, Map.of());

        final Map<String, String> finalAllPathToRealUri =
                java.util.Collections.unmodifiableMap(allPathToRealUri);

        var listener = new LspDiagnosticListener();
        listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);
        ProofResultCollector[] prcRef = {null};
        prcRef[0] = new ProofResultCollector(perFileCallback == null ? null : msym -> {
            javax.tools.JavaFileObject src =
                    msym.enclClass() != null ? msym.enclClass().sourcefile : null;
            if (src == null) { log("[runEscDirWithContext callback] src is null for " + msym); return; }
            String srcName = src.getName();
            String lookupUri;
            try { lookupUri = java.nio.file.Path.of(srcName).toUri().toString(); }
            catch (Exception ex) { log("[runEscDirWithContext callback] URI failed: " + ex); return; }
            String realUri = finalAllPathToRealUri.getOrDefault(srcName, lookupUri);
            List<org.eclipse.lsp4j.Diagnostic> diags = listener.getLspDiagnosticsForUri(lookupUri);
            perFileCallback.accept(realUri, diags, Map.copyOf(prcRef[0].getResults()));
        });
        ProofResultCollector prc = prcRef[0];
        api.setProofResultListener(prc);
        if (onApiReady != null) onApiReady.accept(api);

        List<String> args = buildArgs(settings, "--esc");
        args.addAll(fileList);
        logInvocation("runEscDirWithContext", args);
        log(ts() + " --esc " + fileList.size() + " file(s)" + invocationSuffix(args));
        int rc = api.execute(args.toArray(new String[0]), mockFiles);
        Map<String, List<org.eclipse.lsp4j.Diagnostic>> diagsByUri =
                listener.toLspDiagnosticsAll(finalAllPathToRealUri);
        Map<String, IProverResult.Kind> proofResults = prc.getResults();
        int totalDiags = diagsByUri.values().stream().mapToInt(List::size).sum();
        if (rc == 5)
            log(ts() + " --esc cancelled: " + cancelSummary(proofResults) + ", " + totalDiags + " diagnostic(s)");
        else
            log(ts() + " --esc complete: " + proofResults.size() + " method(s), " + totalDiags + " diagnostic(s)");
        return new DirCheckResult(diagsByUri, rc, proofResults);
    }

    /** Convenience overload with no progressive callback. */
    public static DirCheckResult runEscDirWithContext(
            List<String> paths, Map<String, String> snapshot, OpenJMLSettings settings) {
        return runEscDirWithContext(paths, snapshot, settings, null);
    }

    /** Legacy temp-file implementation of {@link #runEscDirWithContext}, used when
     *  {@link #useMockFiles} is {@code false}. */
    private static DirCheckResult runEscDirWithContextLegacy(
            List<String> paths, Map<String, String> snapshot, OpenJMLSettings settings,
            EscProgressCallback perFileCallback, Consumer<IAPI> onApiReady) {
        Path tempDir = null;
        try {
            tempDir = Files.createTempDirectory("openjml-lsp-esc-");

            Map<String, String> uriToTempPath   = new java.util.HashMap<>();
            Map<String, String> allPathToRealUri = new java.util.LinkedHashMap<>();
            for (Map.Entry<String, String> e : snapshot.entrySet()) {
                String uri     = e.getKey();
                String content = e.getValue();
                try {
                    Path tempFile = writeToTempDir(tempDir, uri, content);
                    uriToTempPath.put(uri, tempFile.toString());
                    allPathToRealUri.put(tempFile.toString(), uri);
                } catch (IOException ex) {
                    System.err.println("[CheckRunner.runEscDirWithContextLegacy] write failed for " + uri + ": " + ex);
                }
            }

            List<String> fileList = new ArrayList<>();
            for (String path : paths) {
                java.nio.file.Path p = java.nio.file.Path.of(path);
                if (Files.isDirectory(p)) {
                    try (var stream = Files.walk(p)) {
                        stream.filter(f -> { String s = f.toString(); return s.endsWith(".java") || s.endsWith(".jml"); })
                              .forEach(f -> {
                                  String diskPath = f.toString();
                                  String diskUri  = f.toUri().toString();
                                  String tempPath = uriToTempPath.get(diskUri);
                                  if (diskPath.endsWith(".java")) {
                                      if (tempPath != null) fileList.add(tempPath);
                                      else { fileList.add(diskPath); allPathToRealUri.put(diskPath, diskUri); }
                                  } else {
                                      if (tempPath == null) allPathToRealUri.put(diskPath, diskUri);
                                  }
                              });
                    } catch (IOException ex) {
                        System.err.println("[CheckRunner.runEscDirWithContextLegacy] walk failed for " + path + ": " + ex);
                    }
                } else {
                    String diskUri  = p.toUri().toString();
                    String tempPath = uriToTempPath.get(diskUri);
                    if (path.endsWith(".jml")) {
                        if (tempPath == null) allPathToRealUri.put(path, diskUri);
                    } else {
                        if (tempPath != null) fileList.add(tempPath);
                        else { fileList.add(path); allPathToRealUri.put(path, diskUri); }
                    }
                }
            }

            if (fileList.isEmpty()) return new DirCheckResult(Map.of(), 0, Map.of());

            final Map<String, String> finalAllPathToRealUri =
                    java.util.Collections.unmodifiableMap(allPathToRealUri);

            var listener = new LspDiagnosticListener();
            listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
            var out = new PrintWriter(new StringWriter());
            var api = IAPI.make(out, listener);
            ProofResultCollector[] prcRef = {null};
            prcRef[0] = new ProofResultCollector(perFileCallback == null ? null : msym -> {
                javax.tools.JavaFileObject src =
                        msym.enclClass() != null ? msym.enclClass().sourcefile : null;
                if (src == null) { log("[runEscDirWithContextLegacy callback] src is null for " + msym); return; }
                String srcName = src.getName();
                String lookupUri;
                try { lookupUri = java.nio.file.Path.of(srcName).toUri().toString(); }
                catch (Exception ex) { log("[runEscDirWithContextLegacy callback] URI failed: " + ex); return; }
                String realUri = finalAllPathToRealUri.getOrDefault(srcName, lookupUri);
                List<org.eclipse.lsp4j.Diagnostic> diags = listener.getLspDiagnosticsForUri(lookupUri);
                perFileCallback.accept(realUri, diags, Map.copyOf(prcRef[0].getResults()));
            });
            ProofResultCollector prc = prcRef[0];
            api.setProofResultListener(prc);
            if (onApiReady != null) onApiReady.accept(api);

            List<String> args = buildArgs(settings, "--esc", tempDir);
            args.addAll(fileList);
            logInvocation("runEscDirWithContextLegacy", args);
            int rc = api.execute(args.toArray(new String[0]));
            Map<String, List<org.eclipse.lsp4j.Diagnostic>> diagsByUri =
                    listener.toLspDiagnosticsAll(finalAllPathToRealUri);
            Map<String, IProverResult.Kind> proofResults = prc.getResults();
            int totalDiags = diagsByUri.values().stream().mapToInt(List::size).sum();
            if (rc == 5)
            log(ts() + " --esc cancelled: " + cancelSummary(proofResults) + ", " + totalDiags + " diagnostic(s)");
        else
            log(ts() + " --esc complete: " + proofResults.size() + " method(s), " + totalDiags + " diagnostic(s)");
            return new DirCheckResult(diagsByUri, rc, proofResults);
        } catch (IOException e) {
            System.err.println("[CheckRunner.runEscDirWithContextLegacy] I/O error: " + e);
            return runEscDir(paths, settings, perFileCallback);
        } finally {
            deleteTempDir(tempDir);
        }
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
        if (rc != 0) {
            StringBuilder sb = new StringBuilder("RAC command args:");
            for (String a : args) sb.append(' ').append(a);
            log(sb.toString());
        }

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
        return runOnContent(uri, content, settings, "--check", null, false, null);
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
        return runOnContentWithContext(uri, content, openContent, settings, "--check", null, false, null);
    }

    /** Run {@code --check} on a file already on disk. */
    public static CheckResult checkFile(String filePath, String uri, OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--check", null, false, null);
    }

    /**
     * Run {@code --esc} on {@code content} for {@code uri}, making all other
     * open (possibly unsaved) files in {@code openContent} visible as in-memory source.
     *
     * <p>Same as {@link #checkWithContext} but runs ESC instead of --check.
     */
    public static CheckResult escWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings) {
        return runOnContentWithContext(uri, content, openContent, settings, "--esc", null, true, null);
    }

    /** Like {@link #escWithContext} but fires {@code onApiReady} after the IAPI is set up. */
    public static CheckResult escWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings,
            Consumer<IAPI> onApiReady) {
        return runOnContentWithContext(uri, content, openContent, settings, "--esc", null, true, onApiReady);
    }

    /**
     * Run {@code --esc} on a single method in {@code content} for {@code uri},
     * with all other open files visible as in-memory source.
     */
    public static CheckResult escMethodWithContext(
            String uri, String content, String methodName,
            Map<String, String> openContent, OpenJMLSettings settings) {
        return runOnContentWithContext(uri, content, openContent, settings, "--esc", methodName, true, null);
    }

    /** Like {@link #escMethodWithContext} but fires {@code onApiReady} after the IAPI is set up. */
    public static CheckResult escMethodWithContext(
            String uri, String content, String methodName,
            Map<String, String> openContent, OpenJMLSettings settings,
            Consumer<IAPI> onApiReady) {
        return runOnContentWithContext(uri, content, openContent, settings, "--esc", methodName, true, onApiReady);
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
        if (useMockFiles) {
            org.openjml.MockFiles mockFiles = new org.openjml.MockFiles();
            Map<String, String> fileArgToRealUri = new java.util.LinkedHashMap<>();
            List<String> filePaths = new ArrayList<>();
            for (Map.Entry<String, String> e : modifiedContent.entrySet()) {
                java.net.URI fileUri = java.net.URI.create(e.getKey());
                MockJavaFileObject jfo = new MockJavaFileObject(fileUri, e.getValue());
                mockFiles.addMockByUri(fileUri.normalize(), jfo);
                // .jml files must be in MockFiles so OpenJML finds them as companion specs,
                // but must NOT be on the command line — OpenJML rejects .jml as explicit args.
                if (!e.getKey().endsWith(".jml")) {
                    fileArgToRealUri.put(jfo.getName(), e.getKey());
                    filePaths.add(jfo.getName());
                }
            }
            // With MockFiles, modified content is served in-memory; no temp dir is needed
            // and MockAwareFileManager intercepts lookups before reaching the sourcepath,
            // so no duplicate-class conflict can arise.
            OpenJMLSettings modifiedSettings = new OpenJMLSettings();
            modifiedSettings.sourcePath  = settings.sourcePath;
            modifiedSettings.specsPath   = buildEffectiveSpecsPath(null, settings);
            modifiedSettings.solversPath = settings.solversPath;
            modifiedSettings.classPath   = settings.classPath;
            var listener = new LspDiagnosticListener();
            var out = new java.io.PrintWriter(new java.io.StringWriter());
            var api = IAPI.make(out, listener);
            List<String> args = buildArgs(modifiedSettings, "--check");
            args.addAll(filePaths);
            logInvocation("checkModifiedFiles", args);
            try {
                api.execute(args.toArray(new String[0]), mockFiles);
            } catch (Throwable t) {
                System.err.println("[CheckRunner.checkModifiedFiles] execute failed: " + t);
            }
            List<org.eclipse.lsp4j.Diagnostic> allDiags = new ArrayList<>();
            for (List<org.eclipse.lsp4j.Diagnostic> diags :
                    listener.toLspDiagnosticsAll(fileArgToRealUri).values()) {
                allDiags.addAll(diags);
            }
            return allDiags;
        }

        Path tempDir = null;
        try {
            tempDir = Files.createTempDirectory("openjml-lsp-rename-");

            // Write all modified files at their package-relative paths and record the mapping.
            // .jml files are written to the temp dir so OpenJML discovers them as companion
            // specs, but are NOT added to filePaths — OpenJML rejects .jml as explicit args.
            Map<String, String> tempPathToRealUri = new java.util.LinkedHashMap<>();
            List<String> filePaths = new ArrayList<>();
            for (Map.Entry<String, String> e : modifiedContent.entrySet()) {
                Path p = writeToTempDir(tempDir, e.getKey(), e.getValue());
                if (!e.getKey().endsWith(".jml")) {
                    tempPathToRealUri.put(p.toString(), e.getKey());
                    filePaths.add(p.toString());
                }
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
        if (useMockFiles) {
            org.openjml.MockFiles mockFiles = new org.openjml.MockFiles();
            Map<String, String> fileArgToRealUri = new java.util.LinkedHashMap<>();
            for (Map.Entry<String, String> e : modifiedContent.entrySet()) {
                java.net.URI fileUri = java.net.URI.create(e.getKey());
                MockJavaFileObject jfo = new MockJavaFileObject(fileUri, e.getValue());
                mockFiles.addMockByUri(fileUri.normalize(), jfo);
                // .jml files must be in MockFiles so OpenJML finds them as companion specs,
                // but must NOT be on the command line — OpenJML rejects .jml as explicit args.
                if (!e.getKey().endsWith(".jml"))
                    fileArgToRealUri.put(jfo.getName(), e.getKey());
            }
            System.err.println("[CheckRunner.checkModifiedFilesAndGetCache/mock] fileArgToRealUri keys:");
            fileArgToRealUri.forEach((k, v) -> System.err.println("[CheckRunner]   jfoName='" + k + "' -> realUri='" + v + "'"));
            // Pass individual files so the IASTListener fires for each compiled file.
            // The -sourcepath handles cross-file resolution; MockAwareFileManager serves
            // modified content for files in modifiedContent, real disk for everything else.
            List<String> filePaths = new ArrayList<>(fileArgToRealUri.keySet());
            OpenJMLSettings modifiedSettings = new OpenJMLSettings();
            modifiedSettings.sourcePath  = buildEffectiveSourcePath(null, settings);
            modifiedSettings.specsPath   = buildEffectiveSpecsPath(null, settings);
            modifiedSettings.solversPath = settings.solversPath;
            modifiedSettings.classPath   = settings.classPath;
            var listener = new LspDiagnosticListener();
            var out = new java.io.PrintWriter(new java.io.StringWriter());
            var api = IAPI.make(out, listener);
            ASTCache freshCache = new ASTCache();
            IAPI.IASTListener astListener = (astCtx, jfo, ast) -> {
                String jfoPath = jfo.toUri().getPath();
                String jfoName = jfo.getName();
                String realUri = fileArgToRealUri.get(jfoPath);
                System.err.println("[CheckRunner.checkModifiedFilesAndGetCache/mock] AST fired:"
                        + " jfoName='" + jfoName + "' jfoPath='" + jfoPath + "' realUri=" + realUri);
                if (realUri != null) {
                    freshCache.put(realUri, astCtx, (JmlCompilationUnit) ast);
                }
            };
            api.setASTListener(astListener);
            List<String> args = buildArgs(modifiedSettings, "--check");
            args.addAll(filePaths);
            logInvocation("checkModifiedFilesAndGetCache", args);
            try {
                api.execute(args.toArray(new String[0]), mockFiles);
            } catch (Throwable t) {
                System.err.println("[CheckRunner.checkModifiedFilesAndGetCache] execute failed: " + t);
            } finally {
                api.removeASTListener(astListener);
            }
            List<org.eclipse.lsp4j.Diagnostic> allDiags = new ArrayList<>();
            for (List<org.eclipse.lsp4j.Diagnostic> diags :
                    listener.toLspDiagnosticsAll(fileArgToRealUri).values()) {
                allDiags.addAll(diags);
            }
            return new CheckAndCacheResult(allDiags, freshCache, fileArgToRealUri);
        }

        Path tempDir = null;
        try {
            tempDir = Files.createTempDirectory("openjml-lsp-rename-");

            // .jml files are written to the temp dir so OpenJML discovers them as companion
            // specs by file-system lookup, but are NOT added to filePaths — OpenJML rejects
            // .jml as explicit command-line arguments.
            Map<String, String> tempPathToRealUri = new java.util.LinkedHashMap<>();
            List<String> filePaths = new ArrayList<>();
            for (Map.Entry<String, String> e : modifiedContent.entrySet()) {
                Path p = writeToTempDir(tempDir, e.getKey(), e.getValue());
                if (!e.getKey().endsWith(".jml")) {
                    tempPathToRealUri.put(p.toString(), e.getKey());
                    filePaths.add(p.toString());
                }
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
                // jfo.toUri().getPath() gives the absolute temp-dir path.
                // Store under the real URI so findSymbolAt (file:// lookup) works.
                String jfoPath = jfo.toUri().getPath();
                String realUri = tempPathToRealUri.get(jfoPath);
                if (realUri != null) {
                    freshCache.put(realUri, astCtx, (JmlCompilationUnit) ast);
                }
            };
            api.setASTListener(astListener);
            List<String> args = buildArgs(modifiedSettings, "--check");
            args.addAll(filePaths);
            logInvocation("checkModifiedFilesAndGetCache", args);
            try {
                api.execute(args.toArray(new String[0]));
            } catch (Throwable t) {
                System.err.println("[CheckRunner.checkModifiedFilesAndGetCache] execute failed: " + t);
            } finally {
                api.removeASTListener(astListener);
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
        listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);
        var prc = new ProofResultCollector();
        api.setProofResultListener(prc);

        if (useMockFiles) {
            org.openjml.MockFiles mockFiles = new org.openjml.MockFiles();
            java.net.URI primaryFileUri = java.net.URI.create(primaryUri);
            MockJavaFileObject primaryJfo = new MockJavaFileObject(primaryFileUri, primaryContent);
            mockFiles.addMockByUri(primaryFileUri.normalize(), primaryJfo);
            List<String> args = buildArgs(settings, "--esc");
            args.add(primaryJfo.getName());
            for (Map.Entry<String, String> e : extraSources.entrySet()) {
                java.net.URI extraUri = java.net.URI.create("file:///" + e.getKey());
                MockJavaFileObject extraJfo = new MockJavaFileObject(extraUri, e.getValue());
                mockFiles.addMockByUri(extraUri.normalize(), extraJfo);
                args.add(extraJfo.getName());
            }
            logInvocation("runEscWithSources", args, primaryContent);
            int rc = api.execute(args.toArray(new String[0]), mockFiles);
            System.err.println("[CheckRunner.runEscWithSources] exit code " + rc);
            return new CheckResult(
                    listener.toLspDiagnostics(primaryJfo.getName(), primaryUri),
                    rc, prc.getResults(),
                    listener.toForeignMessages(primaryJfo.getName()), Map.of());
        }

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
        return runOnContent(uri, content, settings, "--esc", null, true, null);
    }

    /**
     * Run {@code --esc} on in-memory content, calling {@code onApiCreated} with the
     * freshly-constructed {@link IAPI} and a live proof-count supplier, just before
     * {@code api.execute()} is invoked.  The supplier returns the number of final
     * proof results recorded by this run's {@link ProofResultCollector} so far;
     * it is updated in real time as each method proof completes.
     *
     * <p>Tests use this to capture the IAPI for cancellation and to wait until
     * at least N proofs have completed — confirming z3 is actively working on
     * <em>this</em> run — before calling {@link IAPI#cancelEsc()}.
     */
    public static CheckResult runEscWithHook(String uri, String content,
                                             OpenJMLSettings settings,
                                             BiConsumer<IAPI, Supplier<Integer>> onApiCreated) {
        return runOnContent(uri, content, settings, "--esc", null, true, onApiCreated);
    }

    /** Run {@code --esc} on a single method in in-memory content with default settings. */
    public static CheckResult runEscMethod(String uri, String content, String methodName) {
        return runEscMethod(uri, content, methodName, new OpenJMLSettings());
    }

    /** Run {@code --esc} on a single method in in-memory content. */
    public static CheckResult runEscMethod(String uri, String content, String methodName,
                                           OpenJMLSettings settings) {
        return runOnContent(uri, content, settings, "--esc", methodName, true, null);
    }

    /** Run {@code --esc} on a file already on disk. */
    public static CheckResult runEscFile(String filePath, String uri, OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--esc", null, true, null);
    }

    /** Like {@link #runEscFile} but fires {@code onApiReady} after the IAPI is set up. */
    public static CheckResult runEscFile(String filePath, String uri, OpenJMLSettings settings,
                                         Consumer<IAPI> onApiReady) {
        return runOnFile(filePath, uri, settings, "--esc", null, true, onApiReady);
    }

    /** Run {@code --esc} on a single method in a file already on disk. */
    public static CheckResult runEscFileMethod(String filePath, String uri, String methodName,
                                               OpenJMLSettings settings) {
        return runOnFile(filePath, uri, settings, "--esc", methodName, true, null);
    }

    /** Like {@link #runEscFileMethod} but fires {@code onApiReady} after the IAPI is set up. */
    public static CheckResult runEscFileMethod(String filePath, String uri, String methodName,
                                               OpenJMLSettings settings, Consumer<IAPI> onApiReady) {
        return runOnFile(filePath, uri, settings, "--esc", methodName, true, onApiReady);
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

    /**
     * Run {@code --rac --dirs path1 path2 ...} on one or more files or directories.
     *
     * <p>Each path may be a {@code .java} file or a directory; OpenJML processes
     * directory arguments recursively (same behaviour as repeated {@code --dir}).
     * Diagnostics are returned grouped by source-file URI.
     *
     * @param paths     one or more OS paths (files or directories) to compile
     * @param outputDir directory for RAC {@code .class} output; {@code null} or empty
     *                  falls back to {@link OpenJMLSettings#racOutputDir} then {@code "rac-classes"}
     * @param settings  current server settings
     */
    public static DirCheckResult runRacDir(List<String> paths, String outputDir,
                                           OpenJMLSettings settings) {
        var listener = new LspDiagnosticListener();
        var out      = new PrintWriter(new StringWriter());
        var api      = IAPI.make(out, listener);

        List<String> args = buildArgs(settings, "--rac");

        // Resolve and create the RAC output directory.
        String rawDir = (outputDir != null && !outputDir.isEmpty()) ? outputDir
                : (settings.racOutputDir != null && !settings.racOutputDir.isEmpty())
                        ? settings.racOutputDir : "rac-classes";
        java.nio.file.Path outputPath;
        java.nio.file.Path raw = java.nio.file.Paths.get(rawDir);
        if (raw.isAbsolute()) {
            outputPath = raw;
        } else {
            String wsRoot = (settings.workspaceFolderPaths != null
                          && !settings.workspaceFolderPaths.isEmpty())
                    ? settings.workspaceFolderPaths.split(java.io.File.pathSeparator)[0]
                    : (!paths.isEmpty() ? new java.io.File(paths.get(0)).getParent() : ".");
            outputPath = java.nio.file.Paths.get(wsRoot).resolve(raw);
        }
        try {
            java.nio.file.Files.createDirectories(outputPath);
        } catch (java.io.IOException e) {
            System.err.println("[CheckRunner.runRacDir] failed to create output dir: " + e);
        }
        args.add("-d");
        args.add(outputPath.toString());
        args.add("--dirs");
        args.addAll(paths);
        logInvocation("runRacDir", args);
        log(ts() + " --rac --dirs " + paths.size() + " path(s) → " + outputPath);

        int rc;
        try {
            rc = api.execute(args.toArray(new String[0]));
        } catch (Throwable e) {
            System.err.println("[CheckRunner.runRacDir] exception: " + e);
            rc = -1;
        }
        System.err.println("[CheckRunner.runRacDir] exit code " + rc);
        return new DirCheckResult(listener.toLspDiagnosticsByFile(), rc, Map.of());
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
     * {@code javaAst}, cache the specs AST under its real URI in the live tier.
     *
     * <p>This gives go-to-definition direct access to the JML specs AST so that
     * lookups from inside {@code .jml} files work without a Java-URI redirect.
     *
     * @param tempUriToRealUri maps temp-dir file URIs to real workspace URIs,
     *                         or {@code null} when no temp directory is in use
     * @param tempDirPrefix    URI prefix string of the temp directory (used to
     *                         detect and skip unmapped temp-dir paths), or {@code null}
     * @param live             unused — retained for call-site compatibility; always stores in live tier
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
        AST_CACHE.put(specsUri, ctx, specs);
    }

    /**
     * Like {@link #runOnContent} but writes all {@code openContent} files into
     * the same temp directory so the compiler resolves cross-file references
     * against their current in-memory versions rather than the on-disk files.
     */
    private static CheckResult runOnContentWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings,
            String modeFlag, String methodName, boolean collectProofResults,
            Consumer<IAPI> onApiReady) {

        var listener = new LspDiagnosticListener();
        if (content != null) listener.setSourceContent(content);
        if ("--esc".equals(modeFlag)) listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
        var out      = new PrintWriter(new StringWriter());
        var api      = IAPI.make(out, listener);

        ProofResultCollector prc = null;
        if (collectProofResults) {
            prc = new ProofResultCollector();
            api.setProofResultListener(prc);
        }
        if (onApiReady != null) onApiReady.accept(api);

        if (useMockFiles) {
            org.openjml.MockFiles mockFiles = new org.openjml.MockFiles();
            // mockUriToRealUri maps mock URI string → real URI for every dirty file
            // other than the primary.  "Dirty" means open in an editor with unsaved
            // changes — the mock serves in-memory content in place of the on-disk file.
            Map<String, String> mockUriToRealUri = new java.util.HashMap<>();
            for (Map.Entry<String, String> e : openContent.entrySet()) {
                if (e.getKey().equals(uri)) continue;
                java.net.URI dirtyUri = java.net.URI.create(e.getKey());
                MockJavaFileObject dirtyJfo = new MockJavaFileObject(dirtyUri, e.getValue());
                mockFiles.addMockByUri(dirtyUri.normalize(), dirtyJfo);
                mockUriToRealUri.put(dirtyJfo.toUri().toString(), e.getKey());
            }
            // If content is null the file is not open — don't mock it; OpenJML reads from disk.
            final String primaryArg;
            final String primaryIdUri;
            java.net.URI primaryFileUri = java.net.URI.create(uri);
            if (content != null) {
                MockJavaFileObject primaryJfo = new MockJavaFileObject(primaryFileUri, content);
                mockFiles.addMockByUri(primaryFileUri.normalize(), primaryJfo);
                primaryArg   = primaryJfo.getName();
                primaryIdUri = primaryJfo.toUri().toString();
            } else {
                primaryArg   = uriToPath(uri);
                if (primaryArg == null) return new CheckResult(List.of(), 0, Map.of(), List.of(), Map.of());
                primaryIdUri = new java.io.File(primaryArg).toURI().toString();
            }

            List<String> args = buildArgs(settings, modeFlag);  // no temp dir prefix
            if (methodName != null && !methodName.isEmpty()) {
                args.add("--method");
                args.add(methodName);
            }
            args.add(primaryArg);
            logInvocation("runOnContentWithContext", args, content);

            String fname = fileName(uri);
            String methodDesc = (methodName != null && !methodName.isEmpty()) ? " [" + methodName + "]" : "";
            if ("--check".equals(modeFlag)) log(ts() + " --check " + fname + invocationSuffix(args));
            else log(ts() + " --esc " + fname + methodDesc + invocationSuffix(args));

            final Map<String, String> compiledPathToRealUri = new java.util.concurrent.ConcurrentHashMap<>();
            compiledPathToRealUri.put(primaryArg, uri);
            for (Map.Entry<String, String> e : mockUriToRealUri.entrySet()) {
                try {
                    Path p = java.nio.file.Paths.get(java.net.URI.create(e.getKey()));
                    compiledPathToRealUri.put(p.toString(), e.getValue());
                } catch (Exception ignored) {}
            }

            final JmlCompilationUnit[] capturedAst = { null };
            final com.sun.tools.javac.util.Context[] capturedCtx = { null };
            IAPI.IASTListener astListener = (astCtx, jfo, ast) -> {
                String jfoUri = jfo.toUri().toString();
                if (jfoUri.equals(primaryIdUri)) {
                    capturedAst[0] = (JmlCompilationUnit) ast;
                    capturedCtx[0] = astCtx;
                } else {
                    String realUri = mockUriToRealUri.get(jfoUri);
                    if (realUri == null) {
                        // Disk file found via sourcepath — map directly.
                        realUri = jfoUri;
                    }
                    JmlCompilationUnit cu = (JmlCompilationUnit) ast;
                    AST_CACHE.put(realUri, astCtx, cu);
                    cacheSpecsCu(cu, astCtx, mockUriToRealUri, null, true);
                    try {
                        Path p = java.nio.file.Paths.get(java.net.URI.create(jfoUri));
                        compiledPathToRealUri.put(p.toString(), realUri);
                    } catch (Exception ignored) {}
                }
            };
            api.setASTListener(astListener);
            int rc;
            try {
                rc = api.execute(args.toArray(new String[0]), mockFiles);
            } finally {
                api.removeASTListener(astListener);
            }
            System.err.println("[CheckRunner.runOnContentWithContext] exit code " + rc + " (" + modeFlag + ")");
            if (rc != 0) {
                listener.getDiagnostics().forEach(d -> {
                    String src = d.getSource() != null ? d.getSource().toUri().toString() : "?";
                    System.err.println("[CheckRunner.runOnContentWithContext]   diag: "
                            + src + ":" + d.getLineNumber() + " " + d.getMessage(null));
                });
            }

            if (capturedAst[0] != null && "--check".equals(modeFlag)) {
                if (rc == 0) {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0],
                                  api, listener, primaryArg);
                } else {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);
                }
                cacheSpecsCu(capturedAst[0], capturedCtx[0], mockUriToRealUri, null, true);
            }

            Map<String, IProverResult.Kind> proofResults = prc != null ? prc.getResults() : Map.of();
            Map<String, List<org.eclipse.lsp4j.Diagnostic>> allDiags =
                    listener.toLspDiagnosticsAll(compiledPathToRealUri);
            List<org.eclipse.lsp4j.Diagnostic> primaryDiags = allDiags.getOrDefault(uri, List.of());
            if ("--check".equals(modeFlag)) {
                int companionFiles = allDiags.size() - 1;
                int companionTotal = allDiags.values().stream().mapToInt(List::size).sum() - primaryDiags.size();
                String companionNote = companionFiles > 0
                        ? " (+" + companionTotal + " diagnostic(s) in " + companionFiles + " companion file(s))"
                        : "";
                log(ts() + " --check " + fname + ": " + primaryDiags.size() + " diagnostic(s)" + companionNote);
            } else if (proofResults.isEmpty()) {
                log(ts() + " --esc " + fname + ": " + primaryDiags.size() + " diagnostic(s)");
            }
            return new CheckResult(primaryDiags, rc, proofResults,
                    listener.toForeignMessages(primaryArg), allDiags);
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

            // Write target file at its package-relative path, or use disk path if not open.
            final String primaryArg;
            if (content != null) {
                Path tempFile = writeToTempDir(tempDir, uri, content);
                primaryArg = tempFile.toString();
            } else {
                primaryArg = uriToPath(uri);
                if (primaryArg == null) return new CheckResult(List.of(), 0, Map.of(), List.of(), Map.of());
            }

            List<String> args = buildArgs(settings, modeFlag, tempDir);
            if (methodName != null && !methodName.isEmpty()) {
                args.add("--method");
                args.add(methodName);
            }
            args.add(primaryArg);
            logInvocation("runOnContentWithContext", args, content);

            String fname = fileName(uri);
            String methodDesc = (methodName != null && !methodName.isEmpty()) ? " [" + methodName + "]" : "";
            if ("--check".equals(modeFlag)) log(ts() + " --check " + fname + invocationSuffix(args));
            else log(ts() + " --esc " + fname + methodDesc + invocationSuffix(args));

            // compiledPathToRealUri is populated by the AST listener — only files
            // that were actually attributed get an entry.  Start with the target.
            final Map<String, String> compiledPathToRealUri = new java.util.concurrent.ConcurrentHashMap<>();
            compiledPathToRealUri.put(primaryArg, uri);
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
            final String tempTargetUri = new java.io.File(primaryArg).toURI().toString();
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
            api.setASTListener(astListener);
            int rc;
            try {
                rc = api.execute(args.toArray(new String[0]));
            } finally {
                api.removeASTListener(astListener);
            }
            System.err.println("[CheckRunner.runOnContentWithContext] exit code " + rc
                    + " (" + modeFlag + ")");

            // Only --check runs update the target AST cache entry; --esc discards.
            if (capturedAst[0] != null && "--check".equals(modeFlag)) {
                if (rc == 0) {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0],
                                  api, listener, primaryArg);
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
            } else if (proofResults.isEmpty()) {
                log(ts() + " --esc " + fname + ": " + primaryDiags.size() + " diagnostic(s)");
            }
            return new CheckResult(primaryDiags, rc, proofResults,
                    listener.toForeignMessages(primaryArg), allDiags);
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
            String methodName, boolean collectProofResults,
            BiConsumer<IAPI, Supplier<Integer>> onApiCreated) {
        var listener = new LspDiagnosticListener();
        listener.setSourceContent(content);   // precompute line-start offsets for accurate columns
        if ("--esc".equals(modeFlag)) listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);

        ProofResultCollector prc = null;
        if (collectProofResults) {
            prc = new ProofResultCollector();
            api.setProofResultListener(prc);
        }
        // Fire the hook after ProofResultCollector is installed so the count supplier
        // reflects live proof completions from the very start of execute().
        if (onApiCreated != null) {
            final ProofResultCollector prcFinal = prc;
            onApiCreated.accept(api, () -> prcFinal == null ? 0 : prcFinal.getResults().size());
        }

        Path tempDir = null;
        try {
            // Determine the file argument passed to execute(), and optionally a MockFiles
            // container.  When useMockFiles is true the content is served in-memory and
            // no temp directory is created; when false, write a temp file as before.
            final String fileArg;
            final String targetUriStr;
            final org.openjml.MockFiles mockFilesObj;
            if (useMockFiles) {
                java.net.URI fileUri = java.net.URI.create(uri);
                MockJavaFileObject mockJfo = new MockJavaFileObject(fileUri, content);
                mockFilesObj = new org.openjml.MockFiles();
                mockFilesObj.addMockByUri(fileUri.normalize(), mockJfo);
                fileArg = mockJfo.getName();
                targetUriStr = mockJfo.toUri().toString();
            } else {
                tempDir = Files.createTempDirectory("openjml-lsp-");
                Path tempFile = writeToTempDir(tempDir, uri, content);
                mockFilesObj = null;
                fileArg = tempFile.toString();
                targetUriStr = tempFile.toUri().toString();
            }

            List<String> args = buildArgs(settings, modeFlag);
            if (methodName != null && !methodName.isEmpty()) {
                args.add("--method");
                args.add(methodName);
            }
            args.add(fileArg);
            logInvocation("runOnContent", args, content);

            String fname = fileName(uri);
            String methodDesc = (methodName != null && !methodName.isEmpty()) ? " [" + methodName + "]" : "";
            if ("--check".equals(modeFlag)) log(ts() + " --check " + fname + invocationSuffix(args));
            else log(ts() + " --esc " + fname + methodDesc + invocationSuffix(args));

            // Capture AST in local vars so we can store with IAPI after execution.
            // Context guard prevents cross-contamination between concurrent runs that
            // share the same URI (possible when useMockFiles is true).
            final JmlCompilationUnit[] capturedAst = { null };
            final com.sun.tools.javac.util.Context[] capturedCtx = { null };
            IAPI.IASTListener astListener = (ctx, jfo, ast) -> {
                if (ctx != api.context()) return;
                if (jfo.toUri().toString().equals(targetUriStr)) {
                    capturedAst[0] = (JmlCompilationUnit) ast;
                    capturedCtx[0] = ctx;
                }
            };
            api.setASTListener(astListener);
            int rc;
            try {
                rc = mockFilesObj != null
                        ? api.execute(args.toArray(new String[0]), mockFilesObj)
                        : api.execute(args.toArray(new String[0]));
            } finally {
                api.removeASTListener(astListener);
            }
            System.err.println("[CheckRunner.runOnContent] exit code " + rc
                    + " (" + modeFlag + ")");

            // Only --check runs update the AST cache.  --esc runs do not redo attribution;
            // any AST they happen to produce is discarded to preserve the --check entry
            // (and its stored IAPI for the doESC API path).
            if (capturedAst[0] != null && "--check".equals(modeFlag)) {
                if (rc == 0) {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0],
                                  api, listener, fileArg);
                } else {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);  // failed check: basic entry
                }
                cacheSpecsCu(capturedAst[0], capturedCtx[0], null, null, true);
            }

            Map<String, IProverResult.Kind> proofResults =
                    prc != null ? prc.getResults() : Map.of();
            // When --method targets a specific method, retain only that method's result;
            // other methods are SKIPPED by OpenJML and are not meaningful to the caller.
            if (methodName != null && !methodName.isEmpty()) {
                String simpleTarget = methodName.contains(".")
                        ? methodName.substring(methodName.lastIndexOf('.') + 1)
                        : methodName;
                proofResults = proofResults.entrySet().stream()
                        .filter(e -> e.getKey().equals(simpleTarget))
                        .collect(java.util.stream.Collectors.toMap(
                                Map.Entry::getKey, Map.Entry::getValue,
                                (a, b) -> a, java.util.LinkedHashMap::new));
            }
            List<org.eclipse.lsp4j.Diagnostic> diags =
                    listener.toLspDiagnostics(fileArg, uri);
            if ("--check".equals(modeFlag))
                log(ts() + " --check " + fname + ": " + diags.size() + " diagnostic(s)");
            else if (rc == 5)
                log(ts() + " --esc " + fname + " cancelled: " + cancelSummary(proofResults));
            else
                log(ts() + " --esc " + fname + " complete: " + proofResults.size() + " method(s), " + diags.size() + " diagnostic(s)");
            return new CheckResult(diags, rc,
                    proofResults, listener.toForeignMessages(fileArg), Map.of());
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
            String methodName, boolean collectProofResults, Consumer<IAPI> onApiReady) {
        var listener = new LspDiagnosticListener();
        if ("--esc".equals(modeFlag)) listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
        var out = new PrintWriter(new StringWriter());
        var api = IAPI.make(out, listener);

        ProofResultCollector prc = null;
        if (collectProofResults) {
            prc = new ProofResultCollector();
            api.setProofResultListener(prc);
        }
        if (onApiReady != null) onApiReady.accept(api);

        List<String> args = buildArgs(settings, modeFlag);
        if (methodName != null && !methodName.isEmpty()) {
            args.add("--method");
            args.add(methodName);
        }
        args.add(filePath);
        logInvocation("runOnFile", args);

        String fname = fileName(uri);
        String methodDesc = (methodName != null && !methodName.isEmpty()) ? " [" + methodName + "]" : "";
        if ("--check".equals(modeFlag)) log(ts() + " --check " + fname + invocationSuffix(args));
        else log(ts() + " --esc " + fname + methodDesc + invocationSuffix(args));

        // Capture the primary file's AST locally; store with IAPI on successful --check.
        final String fileUriStr = new java.io.File(filePath).toURI().toString();
        final JmlCompilationUnit[] capturedAst = { null };
        final com.sun.tools.javac.util.Context[] capturedCtx = { null };
        IAPI.IASTListener astListener = (ctx, jfo, ast) -> {
            // Guard: only handle callbacks belonging to this IAPI's own context.
            // Necessary when concurrent runs operate on the same real file path.
            if (ctx != api.context()) return;
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
        api.setASTListener(astListener);
        int rc;
        try {
            rc = api.execute(args.toArray(new String[0]));
        } finally {
            api.removeASTListener(astListener);
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
        else if (rc == 5)
            log(ts() + " --esc " + fname + " cancelled: " + cancelSummary(proofResults));
        else if (proofResults.isEmpty())
            log(ts() + " --esc " + fname + ": " + diags.size() + " diagnostic(s)");
        return new CheckResult(diags, rc,
                proofResults, listener.toForeignMessages(filePath), Map.of());
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

    /**
     * Run ESC on all methods in the file for {@code uri} using a fresh {@link IAPI}
     * instance per method — the {@code "fresh"} engine.
     *
     * <p>All methods are submitted concurrently to {@link OpenJMLSettings#escPool}.
     * Each task creates its own IAPI, does a full {@code --esc --method} run, and
     * returns independently.  There is no shared state between tasks so no locking
     * is required, at the cost of re-parsing and re-typechecking the file once per
     * method.
     *
     * <p>When {@code content} is non-null the source is written to a per-task temp
     * file (like {@link #runEscMethod}), which handles virtual URIs used in tests.
     * When {@code content} is null the file must exist on disk.
     *
     * <p>Falls back to a full-file subprocess ESC if the method list cannot be
     * determined (no cached AST and no file on disk).
     *
     * @param content          in-memory source (may be {@code null} for on-disk files)
     * @param onMethodComplete called on a pool thread as each method finishes;
     *                         may be {@code null}
     */
    public static CompletableFuture<CheckResult> runFreshParallelEscFileAsync(
            String uri, String content, OpenJMLSettings settings,
            Consumer<MethodEscResult> onMethodComplete) {
        String filePath = uriToPath(uri);

        // Use the cached AST to enumerate methods; fall back to full ESC if unavailable.
        ASTCache.Entry entry = AST_CACHE.get(uri);
        List<JmlTree.JmlMethodDecl> methods = (entry != null) ? findAllMethods(entry.ast()) : List.of();
        if (methods.isEmpty()) {
            System.err.println("[CheckRunner.runFreshParallelEscFileAsync] no method list for "
                    + uri + " — falling back to full ESC");
            CheckResult result = (content != null)
                    ? runEsc(uri, content, settings)
                    : (filePath != null ? runEscFile(filePath, uri, settings)
                                       : new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of()));
            return CompletableFuture.completedFuture(result);
        }

        String fname = fileName(uri);
        log(ts() + " --esc " + fname + " [fresh-parallel, " + methods.size() + " method(s)]");

        List<CompletableFuture<MethodEscResult>> futures = new ArrayList<>(methods.size());
        for (JmlTree.JmlMethodDecl method : methods) {
            String mname = method.name.toString();
            if ("<init>".equals(mname)) continue;  // constructors via --method cause spec errors

            String fqn = method.sym != null
                    ? method.sym.owner.toString() + "." + mname
                    : mname;

            CompletableFuture<MethodEscResult> f = CompletableFuture
                    .supplyAsync(() -> {
                        CheckResult r = (content != null)
                                ? runEscMethod(uri, content, fqn, settings)
                                : runEscFileMethod(filePath, uri, fqn, settings);
                        // proofResults may be keyed by simple or qualified name; take first entry.
                        IProverResult.Kind kind = r.proofResults().isEmpty() ? null
                                : r.proofResults().values().iterator().next();
                        return new MethodEscResult(mname, kind, r.diagnostics(), r.exitCode());
                    }, settings.escPool)
                    .whenComplete((r, ex) -> {
                        if (r != null && onMethodComplete != null) onMethodComplete.accept(r);
                        if (ex != null) System.err.println(
                                "[CheckRunner.runFreshParallelEscFileAsync] task failed: " + ex);
                    });
            futures.add(f);
        }

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
                    log(ts() + " --esc " + fname + " [fresh-parallel] complete: "
                            + proofResults.size() + " method(s), " + allDiags.size() + " diagnostic(s)");
                    return new CheckResult(allDiags, exitCode, proofResults, List.of(), Map.of());
                });
    }

    /** Blocking wrapper around {@link #runFreshParallelEscFileAsync} (used by tests). */
    public static CheckResult runFreshParallelEscFile(String uri, String content,
                                                      OpenJMLSettings settings) {
        try {
            return runFreshParallelEscFileAsync(uri, content, settings, null).get();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of());
        } catch (ExecutionException e) {
            System.err.println("[CheckRunner.runFreshParallelEscFile] failed: " + e.getCause());
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
     *   <li>{@link OpenJMLSettings#sourcePath} — explicit user setting, if non-empty</li>
     *   <li>{@link OpenJMLSettings#workspaceFolderPaths} — workspace folders from the
     *       LSP {@code initialize} request (fallback for single-project / generic clients)</li>
     *   <li>{@link OpenJMLSettings#classPath} — only appended when no source root is
     *       configured, so compiled dependencies can serve as a source fallback</li>
     * </ol>
     */
    static String buildEffectiveSourcePath(Path prefixDir, OpenJMLSettings settings) {
        List<String> parts = new ArrayList<>();
        if (prefixDir != null) parts.add(prefixDir.toString());
        boolean hasSourcePath = settings.sourcePath != null && !settings.sourcePath.isEmpty();
        if (hasSourcePath) {
            // JDT-resolved source path already covers this project and its dependencies.
            // Do NOT also add workspaceFolderPaths — for default-package
            // files that would introduce a duplicate class source alongside the temp dir,
            // causing javac to silently suppress diagnostics.
            parts.add(settings.sourcePath);
        } else {
            // No explicit source path: fall back to workspaceFolderPaths (single-project
            // / generic clients) or rootPaths (per-project settings object).
            String fallback = (settings.rootPaths != null && !settings.rootPaths.isEmpty())
                    ? settings.rootPaths : settings.workspaceFolderPaths;
            if (fallback != null && !fallback.isEmpty())
                parts.add(fallback);
            if (settings.classPath != null && !settings.classPath.isEmpty())
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
        // Do NOT add workspaceFolderPaths here — project roots are not spec roots.
        // User .jml files are in source folders which are already on the sourcepath.
        parts.add(settings.specsPath);
        return String.join(java.io.File.pathSeparator, parts);
    }

    /** Log an OpenJML invocation to stderr (captured in /tmp/openjml-lsp-debug.log). */
    private static void logInvocation(String caller, List<String> args) {
        logInvocation(caller, args, null);
    }

    private static String firstLine(String s) {
        if (s == null) return "null";
        int nl = s.indexOf('\n');
        return nl >= 0 ? s.substring(0, nl) : s;
    }

    private static void logInvocation(String caller, List<String> args, String content) {
        StringBuilder sb = new StringBuilder();
        sb.append("[CheckRunner.").append(caller).append("] args:");
        for (String a : args) sb.append(' ').append(a);
        sb.append('\n');
        //if (content != null) {
        //    int nl = content.indexOf('\n');
        //    String firstLine = nl >= 0 ? content.substring(0, nl) : content;
        //    String preview = content.length() <= 1000
        //            ? content
        //            : content.substring(0, 1000) + "...[truncated]";
        //    sb.append("  content: ").append(content.length()).append(" chars, first line: ")
        //      .append(firstLine).append('\n');
        //    sb.append("  content preview:\n").append(preview).append('\n');
        //}
        //sb.append("  OPENJML_INSTALL=").append(System.getenv("OPENJML_INSTALL")).append('\n');
        //sb.append("  OPENJML_SPECS=").append(System.getenv("OPENJML_SPECS")).append('\n');
        //sb.append("  OPENJML_SOLVERS=").append(System.getenv("OPENJML_SOLVERS")).append('\n');
        System.err.print(sb);
    }

    /**
     * Extract the value of a single-value flag from an args list, or {@code null}.
     * For example, {@code argValue(args, "-sourcepath")} returns the sourcepath string.
     */
    private static String argValue(List<String> args, String flag) {
        for (int i = 0; i + 1 < args.size(); i++) {
            if (flag.equals(args.get(i))) return args.get(i + 1);
        }
        return null;
    }

    /**
     * Collect all positional file arguments from an args list (entries ending in
     * {@code .java} or {@code .jml} that are not flag values).
     */
    private static List<String> fileArgs(List<String> args) {
        List<String> files = new ArrayList<>();
        boolean skipNext = false;
        for (String a : args) {
            if (skipNext) { skipNext = false; continue; }
            if (a.startsWith("-") || a.startsWith("--")) { skipNext = true; continue; }
            if (a.endsWith(".java") || a.endsWith(".jml")) files.add(a);
        }
        return files;
    }

    /**
     * Format a Console-visible summary of an ESC/check invocation showing the
     * sourcepath and file arguments.  Returns a string suitable for appending to
     * an existing log line.
     */
    private static String invocationSuffix(List<String> args) {
        String sp = argValue(args, "-sourcepath");
        List<String> files = fileArgs(args);
        String method = argValue(args, "--method");
        StringBuilder sb = new StringBuilder();
        if (method != null) sb.append(" --method ").append(method);
        if (!files.isEmpty()) sb.append(" | files: ").append(files);
        if (sp != null) sb.append(" | -sourcepath ").append(sp);
        return sb.toString();
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
    /** Delete a temporary directory tree; silently ignores a {@code null} argument. */
    private static void deleteTempDir(Path tempDir) {
        if (tempDir == null) return;
        try {
            Files.walk(tempDir)
                 .sorted(Comparator.reverseOrder())
                 .forEach(p -> { try { Files.delete(p); } catch (IOException ignored) {} });
        } catch (IOException ignored) {}
    }

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
