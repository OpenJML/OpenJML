package org.openjml.lsp;

import org.openjml.IAPI;
import org.openjml.MockJavaFileObject;
import org.openjml.IProverResult;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.Utils;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import java.io.IOException;
import java.io.PrintWriter;
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
        if (cb != null) cb.accept(ts() + msg);
    }

    /**
     * Callback for tool-level warnings (e.g. unrecognised {@code --warn} key) that
     * should be shown in red in the console and trigger an "Open Preferences" dialog.
     * When {@code null}, {@link #log} is used as a fallback (e.g. in tests).
     */
    private static volatile java.util.function.Consumer<String> toolWarningCallback = null;

    /** Set the callback that handles tool-level warnings. */
    public static void setToolWarningCallback(java.util.function.Consumer<String> cb) {
        toolWarningCallback = cb;
    }

    /** Log a tool-level warning (bad preference value, etc.) in red with a timestamp. */
    static void logToolWarning(String msg) {
        java.util.function.Consumer<String> cb = toolWarningCallback;
        if (cb != null) cb.accept(msg);
        else log(msg); // fallback for tests that only set logCallback
    }

    private static String ts() {
        return "[" + java.time.LocalTime.now()
                .format(java.time.format.DateTimeFormatter.ofPattern("HH:mm:ss")) + "] ";
    }

    /**
     * Log the exit code, dump per-diagnostic debug lines (when {@code rc != 0}),
     * and route tool-level warnings from {@code listener} to the client console.
     *
     * <p>Tool-level warnings (e.g. unrecognised {@code --warn} key) come from
     * {@link LspDiagnosticListener#toGlobalMessages()} and are forwarded via
     * {@link #logToolWarning}, which uses {@code MessageType.Error} so the Eclipse
     * client renders them in red.  The timestamp is added by the client-side console
     * writer ({@code Console.errorlog}), so no prefix is added here.
     */
    private static void postExecute(int rc, String modeFlag, LspDiagnosticListener listener) {
        ServerLog.serverLog("[CheckRunner] exit code " + rc + " (" + modeFlag + ")");
        if (rc != 0) {
            listener.getDiagnostics().forEach(d -> {
                String src = d.getSource() != null ? d.getSource().toUri().toString() : "?";
                ServerLog.serverLog("[CheckRunner]   diag: "
                        + src + ":" + d.getLineNumber() + " " + d.getMessage(null));
            });
        }
        for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
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
                               Map<String, List<org.eclipse.lsp4j.Diagnostic>> allDiagnostics,
                               Map<String, Map<String, List<org.eclipse.lsp4j.Diagnostic>>> diagsByMethod) {
        /** Returns {@code true} when OpenJML reported a catastrophic error (exit codes 3 and 4
         *  are not distinguished — both indicate resource exhaustion, misconfiguration, or
         *  an internal bug). */
        public boolean isInternalError() { return exitCode == 3 || exitCode == 4; }
        /** Returns {@code true} when OpenJML rejected the command line — indicates a server bug. */
        public boolean isCommandLineError() { return exitCode == 2; }
        /** Returns {@code true} when errors in other files (dependencies) prevented ESC. */
        public boolean hasForeignErrors() { return !foreignMessages.isEmpty(); }
        /**
         * Look up a proof result by simple method name, ignoring the class-owner prefix
         * and signature suffix in the FQN+signature key (e.g. {@code "Foo.m(int)"} → {@code "m"}).
         * Returns {@code null} if no entry matches.
         */
        public IProverResult.Kind proofResultForMethod(String simpleName) {
            for (var e : proofResults.entrySet()) {
                if (bareMethodName(e.getKey()).equals(simpleName)) return e.getValue();
            }
            return null;
        }
    }

    /**
     * Extract the simple method name from a FQN+signature proof-result key.
     * e.g. {@code "com.example.Foo.m(int)"} → {@code "m"},
     *      {@code "Foo.m(int)"} → {@code "m"},
     *      {@code "m"} → {@code "m"}.
     *
     * <p>Uses {@code lastIndexOf('(')} so that local-class FQNs that include
     * the enclosing method name (e.g. {@code "Outer.outer().Local.localM(int)"})
     * strip the signature from the correct position.
     */
    public static String bareMethodName(String fqnKey) {
        int p = fqnKey.lastIndexOf('(');
        String noSig = p >= 0 ? fqnKey.substring(0, p) : fqnKey;
        int dot = noSig.lastIndexOf('.');
        return dot >= 0 ? noSig.substring(dot + 1) : noSig;
    }

    /**
     * Look up a proof result by exact FQN+signature key.
     * Returns {@code null} if no entry matches.
     */
    public static IProverResult.Kind lookupResult(
            Map<String, IProverResult.Kind> proofResults, String rawName) {
        return proofResults.get(rawName);
    }

    /**
     * Collects per-method ESC proof results from OpenJML's
     * {@code IProofResultListener}.  COMPLETED events are ignored; all other
     * terminal results are kept.  A RUNNING event signals that a method proof has
     * just started — the optional {@link #onMethodStarted} callback is invoked for
     * these so the LSP layer can update the code lens to CHECKING immediately.
     */
    private static class ProofResultCollector implements IAPI.IProofResultListener {
        private final Map<String, IProverResult.Kind> results = new LinkedHashMap<>();
        private final Map<String, Map<String, List<org.eclipse.lsp4j.Diagnostic>>> diagsByMethod = new LinkedHashMap<>();

        /**
         * Optional listener used to capture per-method diagnostics via window open/close.
         */
        private final LspDiagnosticListener diagListener;

        /**
         * Callback invoked when each method proof terminates with a final result.
         * Receives the method declaration, the proof kind, and the per-method
         * diagnostics so the LSP layer can publish markers immediately.
         */
        private MethodResultCallback onMethodCompleted;

        /**
         * Optional callback invoked when a method proof starts (RUNNING event).
         * Allows the LSP layer to update that method's code lens to CHECKING before
         * the proof result arrives.
         */
        private java.util.function.Consumer<JmlMethodDecl> onMethodStarted;

        /** Count of methods for which a RUNNING (started) event has been received. */
        private final java.util.concurrent.atomic.AtomicInteger startedCount =
                new java.util.concurrent.atomic.AtomicInteger(0);

        ProofResultCollector() { this(null); }
        ProofResultCollector(LspDiagnosticListener listener) {
            this.diagListener = listener;
        }

        void setOnMethodStarted(java.util.function.Consumer<JmlMethodDecl> cb) {
            this.onMethodStarted = cb;
        }

        void setOnMethodCompleted(CheckRunner.MethodResultCallback cb) {
            this.onMethodCompleted = cb;
        }

        int getStartedCount() { return startedCount.get(); }

        @Override
        public void reportProofResult(JmlMethodDecl methodDecl, IProverResult result) {
            IProverResult.Kind kind = result.result();
            if (kind == IProverResult.RUNNING) {
                startedCount.incrementAndGet();
                if (diagListener != null) diagListener.startMethodWindow();
                if (onMethodStarted != null) onMethodStarted.accept(methodDecl);
                return;
            }
            if (kind == IProverResult.COMPLETED) return;
            // Key: canonical FQN from Utils.uniqueSymbolName — matches MethodLensWalker
            // and Utils.filter() for --method matching.
            String key = (methodDecl.sym != null)
                    ? Utils.uniqueSymbolName(methodDecl.sym)
                    : methodDecl.name.toString();
            results.put(key, kind);
            Map<String, List<org.eclipse.lsp4j.Diagnostic>> methodDiags = Map.of();
            if (diagListener != null) {
                methodDiags = diagListener.stopMethodWindow();
                diagsByMethod.put(key, methodDiags);
            }
            // Log immediately so the console shows progress as each method completes.
            // Suppress SKIPPED: these arise from single-method runs targeting a specific
            // method — the other methods in the file are intentionally skipped and logging
            // them adds noise without useful information.
            if (kind != IProverResult.SKIPPED) {
                javax.tools.JavaFileObject src =
                        methodDecl.sym != null && methodDecl.sym.enclClass() != null
                        ? methodDecl.sym.enclClass().sourcefile : methodDecl.sourcefile;
                String fname = src != null ? fileName(src.getName()) : "unknown";
                log(" --esc " + fname + " " + key + ": " + kindLabel(kind));
            }
            if (onMethodCompleted != null) onMethodCompleted.onResult(methodDecl, kind, methodDiags);
        }

        Map<String, IProverResult.Kind> getResults() {
            return Collections.unmodifiableMap(results);
        }

        Map<String, Map<String, List<org.eclipse.lsp4j.Diagnostic>>> getDiagsByMethod() {
            return Collections.unmodifiableMap(diagsByMethod);
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
            Map<String, IProverResult.Kind> proofResults,
            Map<String, Map<String, List<org.eclipse.lsp4j.Diagnostic>>> diagsByMethod) {
        /**
         * Look up a proof result by simple method name, ignoring the class-owner prefix
         * and signature suffix in the FQN+signature key.
         * Returns {@code null} if no entry matches.
         */
        public IProverResult.Kind proofResultForMethod(String simpleName) {
            for (var e : proofResults.entrySet()) {
                if (bareMethodName(e.getKey()).equals(simpleName)) return e.getValue();
            }
            return null;
        }
    }

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
        return runCheckDir(paths, settings, null);
    }

    public static DirCheckResult runCheckDir(List<String> paths, OpenJMLSettings settings,
                                             String projectId) {
        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(System.err, true);
        var api = IAPI.make(out, listener);
        List<String> args = buildArgs(settings, "--check");
        args.add("--dirs");
        args.addAll(paths);
        logInvocation("runCheckDir", args);
        AST_CACHE.clearNavForRoots(paths, projectId);
        IAPI.IASTListener astListener = (ctx, jfo, ast) -> {
            String uri = jfo.toUri().normalize().toString();
            AST_CACHE.putNav(uri, ctx, (JmlCompilationUnit) ast, paths, projectId);
        };
        api.setASTListener(astListener);
        int rc;
        try {
            rc = api.execute(args.toArray(new String[0]));
        } finally {
            api.removeASTListener(astListener);
        }
        ServerLog.serverLog("[CheckRunner.runCheckDir] exit code " + rc
                + " for " + paths.size() + " path(s)");
        for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
        return new DirCheckResult(listener.toLspDiagnosticsByFile(), rc, Map.of(), Map.of());
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
        return runCheckDirWithContext(paths, snapshot, settings, null);
    }

    public static DirCheckResult runCheckDirWithContext(
            List<String> paths, Map<String, String> snapshot, OpenJMLSettings settings,
            String projectId) {
        if (snapshot.isEmpty()) return runCheckDir(paths, settings, projectId);
        if (!useMockFiles) return runCheckDirWithContextLegacy(paths, snapshot, settings, projectId);

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
        java.util.Set<String> seenRealPaths = new java.util.LinkedHashSet<>();
        for (String path : paths) {
            java.nio.file.Path p = java.nio.file.Path.of(path);
            if (Files.isDirectory(p)) {
                walkSourceFiles(p, seenRealPaths, "runCheckDirWithContext", f -> {
                    String diskPath = f.toString();
                    String diskUri  = f.toUri().toString();
                    if (diskPath.endsWith(".java")) {
                        fileList.add(diskPath);
                        allPathToRealUri.put(diskPath, diskUri);
                    } else {
                        allPathToRealUri.put(diskPath, diskUri); // .jml: diagnostic routing only
                    }
                });
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

        if (fileList.isEmpty()) return new DirCheckResult(Map.of(), 0, Map.of(), Map.of());

        var listener = new LspDiagnosticListener();
        var out = new PrintWriter(System.err, true);
        var api = IAPI.make(out, listener);
        List<String> args = buildArgs(settings, "--check");
        args.addAll(fileList);
        logInvocation("runCheckDirWithContext", args);
        Map<String, String> normToReal = new java.util.HashMap<>();
        for (Map.Entry<String, String> e : snapshot.entrySet()) {
            try { normToReal.put(java.net.URI.create(e.getKey()).normalize().toString(), e.getKey()); }
            catch (Exception ignored) {}
        }
        AST_CACHE.clearNavForRoots(paths, projectId);
        IAPI.IASTListener astListener = (astCtx, jfo, ast) -> {
            String jfoUri = jfo.toUri().normalize().toString();
            String realUri = normToReal.getOrDefault(jfoUri, jfoUri);
            try {
                String astSrcUri = ((org.jmlspecs.openjml.JmlTree.JmlCompilationUnit) ast)
                        .sourcefile.toUri().normalize().toString();
                ServerLog.serverLog("[AST listener] jfo=" + jfoUri
                        + (jfoUri.equals(astSrcUri) ? "" : " ast.sourcefile=" + astSrcUri));
            } catch (Exception ignored) {}
            AST_CACHE.putNav(realUri, astCtx,
                    (org.jmlspecs.openjml.JmlTree.JmlCompilationUnit) ast, paths, projectId);
            // Also cache the companion .jml spec CU in the live tier so that
            // codeLensForJml can look it up via ASTCache.get(jmlUri).
            cacheSpecsCu((org.jmlspecs.openjml.JmlTree.JmlCompilationUnit) ast, astCtx,
                         normToReal, null);
        };
        api.setASTListener(astListener);
        int rc;
        try {
            rc = api.execute(args.toArray(new String[0]), mockFiles);
        } finally {
            api.removeASTListener(astListener);
        }
        ServerLog.serverLog("[CheckRunner.runCheckDirWithContext] exit code " + rc
                + " for " + fileList.size() + " file(s)");
        for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
        return new DirCheckResult(listener.toLspDiagnosticsAll(allPathToRealUri), rc, Map.of(), Map.of());
    }

    /** Legacy temp-file implementation of {@link #runCheckDirWithContext}, used when
     *  {@link #useMockFiles} is {@code false}. */
    private static DirCheckResult runCheckDirWithContextLegacy(
            List<String> paths, Map<String, String> snapshot, OpenJMLSettings settings,
            String projectId) {
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
                    ServerLog.serverLog("[CheckRunner.runCheckDirWithContextLegacy] write failed for " + uri + ": " + ex);
                }
            }

            List<String> fileList = new ArrayList<>();
            java.util.Set<String> seenRealPaths = new java.util.LinkedHashSet<>();
            for (String path : paths) {
                java.nio.file.Path p = java.nio.file.Path.of(path);
                if (Files.isDirectory(p)) {
                    walkSourceFiles(p, seenRealPaths, "runCheckDirWithContextLegacy", f -> {
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

            if (fileList.isEmpty()) return new DirCheckResult(Map.of(), 0, Map.of(), Map.of());

            var listener = new LspDiagnosticListener();
            var out = new PrintWriter(System.err, true);
            var api = IAPI.make(out, listener);
            List<String> args = buildArgs(settings, "--check", tempDir);
            args.addAll(fileList);
            logInvocation("runCheckDirWithContextLegacy", args);
            int rc = api.execute(args.toArray(new String[0]));
            ServerLog.serverLog("[CheckRunner.runCheckDirWithContextLegacy] exit code " + rc
                    + " for " + fileList.size() + " file(s)");
            for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
            return new DirCheckResult(listener.toLspDiagnosticsAll(allPathToRealUri), rc, Map.of(), Map.of());
        } catch (IOException e) {
            ServerLog.serverLog("[CheckRunner.runCheckDirWithContextLegacy] I/O error: " + e);
            return runCheckDir(paths, settings, projectId);
        } finally {
            deleteTempDir(tempDir);
        }
    }

    /**
     * Callback invoked after each method's proof completes during an ESC run.
     * Receives the file URI, the simple name of the method whose proof is starting
     * (the RUNNING event), the diagnostics accumulated so far for that file, and a
     * snapshot of the proof results recorded so far (all methods that have finished,
     * keyed by simple method name).  Use the snapshot to update per-method code-lens
     * status incrementally without waiting for the full run.
     *
     * <p>The {@code startingMethod} is the method that just fired a RUNNING event —
     * it has NOT yet been added to {@code proofResultsSoFar}.  Use it to flip that
     * method's code lens to CHECKING while it is being proved.
     */
    @FunctionalInterface
    public interface EscProgressCallback {
        void accept(String uri,
                    String startingMethod,
                    List<org.eclipse.lsp4j.Diagnostic> diagsSoFar,
                    Map<String, IProverResult.Kind> proofResultsSoFar,
                    Map<String, Map<String, List<org.eclipse.lsp4j.Diagnostic>>> diagsByMethodSoFar);
    }

    /**
     * Callback fired by single-file ESC ({@code escWithContext}, {@code runEscFile})
     * immediately after each method proof finishes, before the overall run returns.
     * Allows the LSP layer to update that method's code lens to its final state
     * (VERIFIED/FAILED) incrementally rather than waiting for the whole file to finish.
     */
    @FunctionalInterface
    public interface MethodResultCallback {
        void onResult(JmlMethodDecl methodDecl, IProverResult.Kind kind,
                      Map<String, List<org.eclipse.lsp4j.Diagnostic>> diagsByUri);
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
        var out = new PrintWriter(System.err, true);
        var api = IAPI.make(out, listener);
        ProofResultCollector[] prcRef = {null};
        prcRef[0] = new ProofResultCollector(listener);
        if (perFileCallback != null) prcRef[0].setOnMethodCompleted((methodDecl, kind, ignored) -> {
            javax.tools.JavaFileObject src =
                    methodDecl.sym != null && methodDecl.sym.enclClass() != null
                    ? methodDecl.sym.enclClass().sourcefile : methodDecl.sourcefile;
            if (src == null) { log("[runEscDir callback] src is null for " + methodDecl.name); return; }
            String uri;
            try { uri = java.nio.file.Path.of(src.getName()).toUri().toString(); }
            catch (Exception e) { log("[runEscDir callback] URI conversion failed: " + e); return; }
            List<org.eclipse.lsp4j.Diagnostic> diags = listener.getLspDiagnosticsForUri(uri);
            perFileCallback.accept(uri, methodDecl.name.toString(), diags,
                    Map.copyOf(prcRef[0].getResults()), Map.copyOf(prcRef[0].getDiagsByMethod()));
        });
        ProofResultCollector prc = prcRef[0];
        // Fire callback with null diags on RUNNING events so callers can flip to CHECKING early.
        if (perFileCallback != null) {
            prc.setOnMethodStarted(methodDecl -> {
                javax.tools.JavaFileObject src =
                        methodDecl.sym != null && methodDecl.sym.enclClass() != null
                        ? methodDecl.sym.enclClass().sourcefile : methodDecl.sourcefile;
                if (src == null) return;
                String onUri;
                try { onUri = java.nio.file.Path.of(src.getName()).toUri().toString(); }
                catch (Exception e) { return; }
                perFileCallback.accept(onUri, methodDecl.name.toString(), null, null, null);
            });
        }
        api.setProofResultListener(prc);
        IAPI.IASTListener astListener = (ctx, jfo, ast) -> {
            String uri = jfo.toUri().normalize().toString();
            AST_CACHE.put(uri, ctx, (JmlCompilationUnit) ast);
            cacheSpecsCu((JmlCompilationUnit) ast, ctx, null, null);
        };
        api.setASTListener(astListener);
        if (onApiReady != null) onApiReady.accept(api);

        List<String> args = buildArgs(settings, "--esc");
        args.add("--dirs");
        args.addAll(paths);
        logInvocation("runEscDir", args);
        log(" --esc --dirs " + paths + invocationSuffix(args));
        int rc = api.execute(args.toArray(new String[0]));
        api.removeASTListener(astListener);
        Map<String, List<org.eclipse.lsp4j.Diagnostic>> diagsByUri = listener.toLspDiagnosticsByFile();
        Map<String, IProverResult.Kind> proofResults = prc.getResults();
        int totalDiags = diagsByUri.values().stream().mapToInt(List::size).sum();
        if (rc == 5)
            log(" --esc cancelled: " + cancelSummary(proofResults) + ", " + totalDiags + " diagnostic(s)");
        else
            log(" --esc complete: " + proofResults.size() + " method(s), " + totalDiags + " diagnostic(s)");
        for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
        return new DirCheckResult(diagsByUri, rc, proofResults, prc.getDiagsByMethod());
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
        java.util.Set<String> seenRealPaths = new java.util.LinkedHashSet<>();
        for (String path : paths) {
            java.nio.file.Path p = java.nio.file.Path.of(path);
            if (Files.isDirectory(p)) {
                walkSourceFiles(p, seenRealPaths, "runEscDirWithContext", f -> {
                    String diskPath = f.toString();
                    String diskUri  = f.toUri().toString();
                    if (diskPath.endsWith(".java")) {
                        fileList.add(diskPath);
                        allPathToRealUri.put(diskPath, diskUri);
                    } else {
                        allPathToRealUri.put(diskPath, diskUri);
                    }
                });
            } else {
                String diskUri = p.toUri().toString();
                if (path.endsWith(".jml")) allPathToRealUri.put(path, diskUri);
                else { fileList.add(path); allPathToRealUri.put(path, diskUri); }
            }
        }

        if (fileList.isEmpty()) return new DirCheckResult(Map.of(), 0, Map.of(), Map.of());

        final Map<String, String> finalAllPathToRealUri =
                java.util.Collections.unmodifiableMap(allPathToRealUri);

        var listener = new LspDiagnosticListener();
        listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
        var out = new PrintWriter(System.err, true);
        var api = IAPI.make(out, listener);
        ProofResultCollector[] prcRef = {null};
        prcRef[0] = new ProofResultCollector(listener);
        if (perFileCallback != null) prcRef[0].setOnMethodCompleted((methodDecl, kind, ignored) -> {
            javax.tools.JavaFileObject src =
                    methodDecl.sym != null && methodDecl.sym.enclClass() != null
                    ? methodDecl.sym.enclClass().sourcefile : methodDecl.sourcefile;
            if (src == null) { log("[runEscDirWithContext callback] src is null for " + methodDecl.name); return; }
            String srcName = src.getName();
            String lookupUri;
            try { lookupUri = java.nio.file.Path.of(srcName).toUri().toString(); }
            catch (Exception ex) { log("[runEscDirWithContext callback] URI failed: " + ex); return; }
            String realUri = finalAllPathToRealUri.getOrDefault(srcName, lookupUri);
            List<org.eclipse.lsp4j.Diagnostic> diags = listener.getLspDiagnosticsForUri(lookupUri);
            perFileCallback.accept(realUri, methodDecl.name.toString(), diags,
                    Map.copyOf(prcRef[0].getResults()), Map.copyOf(prcRef[0].getDiagsByMethod()));
        });
        ProofResultCollector prc = prcRef[0];
        // Fire callback with null diags on RUNNING events so callers can flip to CHECKING early.
        if (perFileCallback != null) {
            prc.setOnMethodStarted(methodDecl -> {
                javax.tools.JavaFileObject src =
                        methodDecl.sym != null && methodDecl.sym.enclClass() != null
                        ? methodDecl.sym.enclClass().sourcefile : methodDecl.sourcefile;
                if (src == null) return;
                String srcName = src.getName();
                String onUri;
                try { onUri = finalAllPathToRealUri.getOrDefault(srcName,
                        java.nio.file.Path.of(srcName).toUri().toString()); }
                catch (Exception ex) { return; }
                perFileCallback.accept(onUri, methodDecl.name.toString(), null, null, null);
            });
        }
        api.setProofResultListener(prc);
        IAPI.IASTListener escAstListener = (ctx, jfo, ast) -> {
            String jfoUri = jfo.toUri().normalize().toString();
            String realUri = finalAllPathToRealUri.getOrDefault(jfo.getName(), jfoUri);
            AST_CACHE.put(realUri, ctx, (JmlCompilationUnit) ast);
            cacheSpecsCu((JmlCompilationUnit) ast, ctx, finalAllPathToRealUri, null);
        };
        api.setASTListener(escAstListener);
        if (onApiReady != null) onApiReady.accept(api);

        List<String> args = buildArgs(settings, "--esc");
        args.addAll(fileList);
        logInvocation("runEscDirWithContext", args);
        log(" --esc " + fileList.size() + " file(s)" + invocationSuffix(args));
        int rc = api.execute(args.toArray(new String[0]), mockFiles);
        api.removeASTListener(escAstListener);
        Map<String, List<org.eclipse.lsp4j.Diagnostic>> diagsByUri =
                listener.toLspDiagnosticsAll(finalAllPathToRealUri);
        Map<String, IProverResult.Kind> proofResults = prc.getResults();
        int totalDiags = diagsByUri.values().stream().mapToInt(List::size).sum();
        if (rc == 5)
            log(" --esc cancelled: " + cancelSummary(proofResults) + ", " + totalDiags + " diagnostic(s)");
        else
            log(" --esc complete: " + proofResults.size() + " method(s), " + totalDiags + " diagnostic(s)");
        for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
        return new DirCheckResult(diagsByUri, rc, proofResults, prc.getDiagsByMethod());
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
                    ServerLog.serverLog("[CheckRunner.runEscDirWithContextLegacy] write failed for " + uri + ": " + ex);
                }
            }

            List<String> fileList = new ArrayList<>();
            java.util.Set<String> seenRealPaths = new java.util.LinkedHashSet<>();
            for (String path : paths) {
                java.nio.file.Path p = java.nio.file.Path.of(path);
                if (Files.isDirectory(p)) {
                    walkSourceFiles(p, seenRealPaths, "runEscDirWithContextLegacy", f -> {
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

            if (fileList.isEmpty()) return new DirCheckResult(Map.of(), 0, Map.of(), Map.of());

            final Map<String, String> finalAllPathToRealUri =
                    java.util.Collections.unmodifiableMap(allPathToRealUri);

            var listener = new LspDiagnosticListener();
            listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
            var out = new PrintWriter(System.err, true);
            var api = IAPI.make(out, listener);
            ProofResultCollector[] prcRef = {null};
            prcRef[0] = new ProofResultCollector(listener);
            if (perFileCallback != null) prcRef[0].setOnMethodCompleted((methodDecl, kind, ignored) -> {
                javax.tools.JavaFileObject src =
                        methodDecl.sym != null && methodDecl.sym.enclClass() != null
                        ? methodDecl.sym.enclClass().sourcefile : methodDecl.sourcefile;
                if (src == null) { log("[runEscDirWithContextLegacy callback] src is null for " + methodDecl.name); return; }
                String srcName = src.getName();
                String lookupUri;
                try { lookupUri = java.nio.file.Path.of(srcName).toUri().toString(); }
                catch (Exception ex) { log("[runEscDirWithContextLegacy callback] URI failed: " + ex); return; }
                String realUri = finalAllPathToRealUri.getOrDefault(srcName, lookupUri);
                List<org.eclipse.lsp4j.Diagnostic> diags = listener.getLspDiagnosticsForUri(lookupUri);
                perFileCallback.accept(realUri, methodDecl.name.toString(), diags,
                        Map.copyOf(prcRef[0].getResults()), Map.copyOf(prcRef[0].getDiagsByMethod()));
            });
            ProofResultCollector prc = prcRef[0];
            // Fire callback with null diags on RUNNING events so callers can flip to CHECKING early.
            if (perFileCallback != null) {
                prc.setOnMethodStarted(methodDecl -> {
                    javax.tools.JavaFileObject src =
                            methodDecl.sym != null && methodDecl.sym.enclClass() != null
                            ? methodDecl.sym.enclClass().sourcefile : methodDecl.sourcefile;
                    if (src == null) return;
                    String srcName = src.getName();
                    String onUri;
                    try { onUri = finalAllPathToRealUri.getOrDefault(srcName,
                            java.nio.file.Path.of(srcName).toUri().toString()); }
                    catch (Exception ex) { return; }
                    perFileCallback.accept(onUri, methodDecl.name.toString(), null, null, null);
                });
            }
            api.setProofResultListener(prc);
            final String legacyTempPrefix = tempDir.toUri().toString();
            IAPI.IASTListener legacyAstListener = (ctx, jfo, ast) -> {
                String jfoUri = jfo.toUri().normalize().toString();
                String realUri = finalAllPathToRealUri.getOrDefault(jfo.getName(), null);
                if (realUri == null && !jfoUri.startsWith(legacyTempPrefix)) realUri = jfoUri;
                if (realUri == null) return;
                AST_CACHE.put(realUri, ctx, (JmlCompilationUnit) ast);
                cacheSpecsCu((JmlCompilationUnit) ast, ctx, finalAllPathToRealUri, legacyTempPrefix);
            };
            api.setASTListener(legacyAstListener);
            if (onApiReady != null) onApiReady.accept(api);

            List<String> args = buildArgs(settings, "--esc", tempDir);
            args.addAll(fileList);
            logInvocation("runEscDirWithContextLegacy", args);
            int rc = api.execute(args.toArray(new String[0]));
            api.removeASTListener(legacyAstListener);
            Map<String, List<org.eclipse.lsp4j.Diagnostic>> diagsByUri =
                    listener.toLspDiagnosticsAll(finalAllPathToRealUri);
            Map<String, IProverResult.Kind> proofResults = prc.getResults();
            int totalDiags = diagsByUri.values().stream().mapToInt(List::size).sum();
            if (rc == 5)
            log(" --esc cancelled: " + cancelSummary(proofResults) + ", " + totalDiags + " diagnostic(s)");
        else
            log(" --esc complete: " + proofResults.size() + " method(s), " + totalDiags + " diagnostic(s)");
            for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
            return new DirCheckResult(diagsByUri, rc, proofResults, prc.getDiagsByMethod());
        } catch (IOException e) {
            ServerLog.serverLog("[CheckRunner.runEscDirWithContextLegacy] I/O error: " + e);
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
        var out = new PrintWriter(System.err, true);
        var api = IAPI.make(out, listener);

        ServerLog.serverLog("[runRacPaths] settings: sourcePath=" + settings.sourcePath
                + " classPath=" + settings.classPath
                + " specsPath=" + settings.specsPath
                + " racOutputDir=" + settings.racOutputDir
                + " javaOutputDir=" + settings.javaOutputDir
                + " rootPaths=" + settings.rootPaths
                + " workspaceFolderPaths=" + settings.clientSettings.workspaceFolderPaths);
        List<String> args = buildArgs(settings, "--rac");

        // Resolve and create the RAC output directory.
        String rawDir = (settings.racOutputDir != null && !settings.racOutputDir.isEmpty())
                ? settings.racOutputDir : "bin";
        java.nio.file.Path raw = java.nio.file.Paths.get(rawDir);
        java.nio.file.Path outputPath;
        if (raw.isAbsolute()) {
            outputPath = raw;
        } else {
            // Prefer a workspace root; fall back to the first workspaceFolderPath;
            // only use "." as a last resort (which gives a relative -d path).
            List<String> effectiveRoots = settings.effectiveRoots();
            String wsRoot;
            if (!effectiveRoots.isEmpty()) {
                wsRoot = effectiveRoots.get(0);
            } else if (settings.clientSettings.workspaceFolderPaths != null
                    && !settings.clientSettings.workspaceFolderPaths.isBlank()) {
                wsRoot = settings.clientSettings.workspaceFolderPaths.split("[;:]")[0];
            } else {
                wsRoot = ".";
            }
            outputPath = java.nio.file.Paths.get(wsRoot).resolve(raw);
        }
        try { java.nio.file.Files.createDirectories(outputPath); }
        catch (java.io.IOException e) {
            ServerLog.serverLog("[CheckRunner.runRacPaths] failed to create output dir: " + e);
        }
        args.add("-d");
        args.add(outputPath.toString());
        args.add("--dirs");
        args.addAll(paths);
        logInvocation("runRacPaths", args);
        int rc = api.execute(args.toArray(new String[0]));
        ServerLog.serverLog("[CheckRunner.runRacPaths] exit code " + rc
                + " for " + paths.size() + " path(s)");
        if (rc != 0) {
            StringBuilder sb = new StringBuilder("RAC command args:");
            for (String a : args) sb.append(' ').append(a);
            log(sb.toString());
        }
        for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
        return new CheckResult(List.of(), rc, Map.of(), List.of(),
                listener.toLspDiagnosticsByFile(), Map.of());
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
     * <p>Same as {@link #checkWithContext} but runs ESC instead of {@code --check}.
     * {@code onApiReady} fires once the IAPI is set up (use to register cancellation hooks).
     * {@code onMethodStarted} fires each time a method proof begins (RUNNING event),
     * allowing the caller to update the code lens to CHECKING before the result arrives.
     */
    public static CheckResult escWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings,
            Consumer<IAPI> onApiReady,
            java.util.function.Consumer<JmlMethodDecl> onMethodStarted) {
        return escWithContext(uri, content, openContent, settings, onApiReady, onMethodStarted, null);
    }

    public static CheckResult escWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings,
            Consumer<IAPI> onApiReady,
            java.util.function.Consumer<JmlMethodDecl> onMethodStarted,
            MethodResultCallback onMethodCompleted) {
        return runOnContentWithContext(uri, content, openContent, settings, "--esc", null, true,
                onApiReady, onMethodStarted, onMethodCompleted);
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
            modifiedSettings.classPath   = settings.classPath;
            var listener = new LspDiagnosticListener();
            var out = new java.io.PrintWriter(System.err, true);
            var api = IAPI.make(out, listener);
            List<String> args = buildArgs(modifiedSettings, "--check");
            args.addAll(filePaths);
            logInvocation("checkModifiedFiles", args);
            try {
                api.execute(args.toArray(new String[0]), mockFiles);
            } catch (Throwable t) {
                ServerLog.serverLog("[CheckRunner.checkModifiedFiles] execute failed: " + t);
            }
            for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
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
            modifiedSettings.classPath       = settings.classPath;

            // Run a single --check invocation on all files so cross-file dependencies
            // (e.g., A.java referencing a renamed symbol in B.java) are caught.
            var listener = new LspDiagnosticListener();
            var out = new java.io.PrintWriter(System.err, true);
            var api = IAPI.make(out, listener);
            List<String> args = buildArgs(modifiedSettings, "--check");
            args.addAll(filePaths);
            logInvocation("checkModifiedFiles", args);
            try {
                api.execute(args.toArray(new String[0]));
            } catch (Throwable t) {
                ServerLog.serverLog("[CheckRunner.checkModifiedFiles] execute failed: " + t);
            }
            for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
            // Collect all diagnostics across files.
            List<org.eclipse.lsp4j.Diagnostic> allDiags = new ArrayList<>();
            for (List<org.eclipse.lsp4j.Diagnostic> diags :
                    listener.toLspDiagnosticsAll(tempPathToRealUri).values()) {
                allDiags.addAll(diags);
            }
            return allDiags;
        } catch (IOException e) {
            ServerLog.serverLog("[CheckRunner.checkModifiedFiles] I/O error: " + e);
            return List.of();
        } finally {
            deleteTempDir(tempDir);
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
            ServerLog.serverLog("[CheckRunner.checkModifiedFilesAndGetCache/mock] fileArgToRealUri keys:");
            fileArgToRealUri.forEach((k, v) -> ServerLog.serverLog("[CheckRunner]   jfoName='" + k + "' -> realUri='" + v + "'"));
            // Pass individual files so the IASTListener fires for each compiled file.
            // The -sourcepath handles cross-file resolution; MockAwareFileManager serves
            // modified content for files in modifiedContent, real disk for everything else.
            List<String> filePaths = new ArrayList<>(fileArgToRealUri.keySet());
            OpenJMLSettings modifiedSettings = new OpenJMLSettings();
            modifiedSettings.sourcePath  = buildEffectiveSourcePath(null, settings);
            modifiedSettings.specsPath   = buildEffectiveSpecsPath(null, settings);
            modifiedSettings.classPath   = settings.classPath;
            var listener = new LspDiagnosticListener();
            var out = new java.io.PrintWriter(System.err, true);
            var api = IAPI.make(out, listener);
            ASTCache freshCache = new ASTCache();
            IAPI.IASTListener astListener = (astCtx, jfo, ast) -> {
                String jfoPath = jfo.toUri().getPath();
                String jfoName = jfo.getName();
                String realUri = fileArgToRealUri.get(jfoPath);
                ServerLog.serverLog("[CheckRunner.checkModifiedFilesAndGetCache/mock] AST fired:"
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
                ServerLog.serverLog("[CheckRunner.checkModifiedFilesAndGetCache] execute failed: " + t);
            } finally {
                api.removeASTListener(astListener);
            }
            for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
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
            modifiedSettings.classPath   = settings.classPath;

            var listener = new LspDiagnosticListener();
            var out = new java.io.PrintWriter(System.err, true);
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
                ServerLog.serverLog("[CheckRunner.checkModifiedFilesAndGetCache] execute failed: " + t);
            } finally {
                api.removeASTListener(astListener);
            }
            for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
            List<org.eclipse.lsp4j.Diagnostic> allDiags = new ArrayList<>();
            for (List<org.eclipse.lsp4j.Diagnostic> diags :
                    listener.toLspDiagnosticsAll(tempPathToRealUri).values()) {
                allDiags.addAll(diags);
            }
            return new CheckAndCacheResult(allDiags, freshCache, tempPathToRealUri);
        } catch (IOException e) {
            ServerLog.serverLog("[CheckRunner.checkModifiedFilesAndGetCache] I/O error: " + e);
            return new CheckAndCacheResult(List.of(), new ASTCache(), Map.of());
        } finally {
            deleteTempDir(tempDir);
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
        var out = new PrintWriter(System.err, true);
        var api = IAPI.make(out, listener);
        var prc = new ProofResultCollector(listener);
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
            ServerLog.serverLog("[CheckRunner.runEscWithSources] exit code " + rc);
            for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
            return new CheckResult(
                    listener.toLspDiagnostics(primaryJfo.getName(), primaryUri),
                    rc, prc.getResults(),
                    listener.toForeignMessages(primaryJfo.getName()), Map.of(),
                    prc.getDiagsByMethod());
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
            ServerLog.serverLog("[CheckRunner.runEscWithSources] exit code " + rc);
            for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
            return new CheckResult(
                    listener.toLspDiagnostics(tempFile.toString(), primaryUri),
                    rc, prc.getResults(),
                    listener.toForeignMessages(tempFile.toString()), Map.of(),
                    prc.getDiagsByMethod());
        } catch (IOException e) {
            ServerLog.serverLog("[CheckRunner.runEscWithSources] I/O error: " + e);
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of(), Map.of());
        } finally {
            deleteTempDir(tempDir);
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
        return runOnFile(filePath, uri, settings, "--esc", null, true, onApiReady, null);
    }

    /**
     * Like {@link #runEscFile(String, String, OpenJMLSettings, Consumer)} but also
     * fires {@code onMethodStarted} each time a method proof begins (RUNNING event).
     */
    public static CheckResult runEscFile(String filePath, String uri, OpenJMLSettings settings,
                                         Consumer<IAPI> onApiReady,
                                         java.util.function.Consumer<JmlMethodDecl> onMethodStarted) {
        return runOnFile(filePath, uri, settings, "--esc", null, true, onApiReady, onMethodStarted, null);
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
     * {@link OpenJMLSettings#racOutputDir} (resolved against the project source
     * root when relative).  The output directory is
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
     * Delegates to {@link #runRacPaths} with a single-element path list.
     * If {@code outputDir} is non-null it overrides {@link OpenJMLSettings#racOutputDir}.
     */
    public static CheckResult runRacFile(String filePath, String uri, OpenJMLSettings settings,
                                          String outputDir) {
        OpenJMLSettings s = settings;
        if (outputDir != null && !outputDir.isEmpty()) {
            s = new OpenJMLSettings(settings);
            s.racOutputDir = outputDir;
        }
        CheckResult r = runRacPaths(List.of(filePath), s);
        List<org.eclipse.lsp4j.Diagnostic> fileDiags =
                r.allDiagnostics().getOrDefault(uri, List.of());
        return new CheckResult(fileDiags, r.exitCode(), Map.of(), List.of(), r.allDiagnostics(), Map.of());
    }

    /**
     * Delegates to {@link #runRacPaths} with a {@code DirCheckResult} return type.
     * If {@code outputDir} is non-null it overrides {@link OpenJMLSettings#racOutputDir}.
     */
    public static DirCheckResult runRacDir(List<String> paths, String outputDir,
                                           OpenJMLSettings settings) {
        OpenJMLSettings s = settings;
        if (outputDir != null && !outputDir.isEmpty()) {
            s = new OpenJMLSettings(settings);
            s.racOutputDir = outputDir;
        }
        CheckResult r = runRacPaths(paths, s);
        return new DirCheckResult(r.allDiagnostics(), r.exitCode(), Map.of(), Map.of());
    }

    // --- utility ---

    /**
     * Walk {@code dir} following symlinks, filter to {@code .java} and {@code .jml}
     * files, deduplicate by real path, and pass each unique file to {@code consumer}.
     *
     * <p>Using {@link java.nio.file.FileVisitOption#FOLLOW_LINKS} ensures that
     * symlinked subdirectories (e.g. Eclipse linked folders) are entered.
     * Deduplication by {@link java.nio.file.Path#toRealPath()} prevents the same
     * physical file from being compiled twice when it is reachable via multiple
     * symlink paths.  A {@link java.nio.file.FileSystemLoopException} (cycle) or
     * other {@link IOException} terminates the walk early but does not propagate,
     * so files discovered before the cycle are still compiled.
     *
     * @param seenRealPaths mutable set shared across all roots in one check run
     */
    private static void walkSourceFiles(java.nio.file.Path dir,
            java.util.Set<String> seenRealPaths, String label,
            java.util.function.Consumer<java.nio.file.Path> consumer) {
        try (var stream = Files.walk(dir, java.nio.file.FileVisitOption.FOLLOW_LINKS)) {
            stream.filter(f -> { String s = f.toString(); return s.endsWith(".java") || s.endsWith(".jml"); })
                  .forEach(f -> {
                      String realPath;
                      try { realPath = f.toRealPath().toString(); }
                      catch (IOException e) { realPath = f.normalize().toAbsolutePath().toString(); }
                      if (!seenRealPaths.add(realPath)) return;
                      consumer.accept(f);
                  });
        } catch (IOException | java.io.UncheckedIOException ex) {
            ServerLog.serverLog("[CheckRunner." + label + "] walk failed for " + dir + ": " + ex);
        }
    }

    /**
     * Convert a {@code file://} URI to an absolute file path, or {@code null}
     * if the URI is not a file URI or cannot be parsed.
     * Returns the path component of {@code uri} without resolving symlinks,
     * so that the path matches whatever key the client and AST listener used.
     */
    public static String uriToPath(String uri) {
        try {
            return URI.create(uri).getPath();
        } catch (Exception e) {
            return null;
        }
    }

    /**
     * Canonicalize {@code uri} by resolving symlinks and normalizing the path.
     * Returns the input unchanged if the URI cannot be parsed or the path does
     * not exist (the fall-through keeps the server functional during early
     * initialization when workspace roots may not yet be on disk).
     */
    public static String canonicalUri(String uri) {
        if (uri == null) return null;
        try {
            java.nio.file.Path p = java.nio.file.Path.of(java.net.URI.create(uri));
            try {
                return p.toRealPath().toUri().toString();
            } catch (java.io.IOException e) {
                return p.normalize().toAbsolutePath().toUri().toString();
            }
        } catch (Exception e) {
            return uri;
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
     */
    private static void cacheSpecsCu(JmlCompilationUnit javaAst, Context ctx,
                                     Map<String, String> tempUriToRealUri,
                                     String tempDirPrefix) {
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
     * Run OpenJML on {@code content} for {@code uri}, supplying all other open
     * files in {@code openContent} as context so cross-file references resolve
     * against their current in-memory versions.
     *
     * <p>Pass {@link java.util.Map#of()} as {@code openContent} for a single-file
     * run with no companions (equivalent to the old {@code runOnContent}).
     */
    private static CheckResult runOnContentWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings,
            String modeFlag, String methodName, boolean collectProofResults,
            Consumer<IAPI> onApiReady) {
        return runOnContentWithContext(uri, content, openContent, settings,
                modeFlag, methodName, collectProofResults,
                onApiReady == null ? null : (api, n) -> onApiReady.accept(api), null, null);
    }

    private static CheckResult runOnContentWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings,
            String modeFlag, String methodName, boolean collectProofResults,
            Consumer<IAPI> onApiReady,
            java.util.function.Consumer<JmlMethodDecl> onMethodStarted) {
        return runOnContentWithContext(uri, content, openContent, settings,
                modeFlag, methodName, collectProofResults,
                onApiReady == null ? null : (api, n) -> onApiReady.accept(api), onMethodStarted, null);
    }

    private static CheckResult runOnContentWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings,
            String modeFlag, String methodName, boolean collectProofResults,
            Consumer<IAPI> onApiReady,
            java.util.function.Consumer<JmlMethodDecl> onMethodStarted,
            MethodResultCallback onMethodCompleted) {
        return runOnContentWithContext(uri, content, openContent, settings,
                modeFlag, methodName, collectProofResults,
                onApiReady == null ? null : (api, n) -> onApiReady.accept(api), onMethodStarted, onMethodCompleted);
    }

    /**
     * Core implementation: run OpenJML on {@code content} for {@code uri} with
     * all {@code openContent} files written as context.  The {@code onApiReady}
     * BiConsumer receives the live {@link IAPI} and a supplier for the running
     * proof-completion count immediately before {@code api.execute()} is called.
     */
    private static CheckResult runOnContentWithContext(
            String uri, String content,
            Map<String, String> openContent, OpenJMLSettings settings,
            String modeFlag, String methodName, boolean collectProofResults,
            BiConsumer<IAPI, Supplier<Integer>> onApiReady,
            java.util.function.Consumer<JmlMethodDecl> onMethodStarted,
            MethodResultCallback onMethodCompleted) {

        var listener = new LspDiagnosticListener();
        if (content != null) listener.setSourceContent(content);
        if ("--esc".equals(modeFlag)) listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
        var out      = new PrintWriter(System.err, true);
        var api      = IAPI.make(out, listener);

        ProofResultCollector prc = null;
        if (collectProofResults) {
            prc = new ProofResultCollector(listener);
            if (onMethodStarted   != null) prc.setOnMethodStarted(onMethodStarted);
            if (onMethodCompleted != null) prc.setOnMethodCompleted(onMethodCompleted);
            api.setProofResultListener(prc);
        }
        if (onApiReady != null) {
            final ProofResultCollector prcFinal = prc;
            onApiReady.accept(api, () -> prcFinal == null ? 0 : prcFinal.getStartedCount());
        }

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
                if (primaryArg == null) return new CheckResult(List.of(), 0, Map.of(), List.of(), Map.of(), Map.of());
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
            if ("--check".equals(modeFlag)) log(" --check " + fname + invocationSuffix(args));
            else log(" --esc " + fname + methodDesc + invocationSuffix(args));

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
                    cacheSpecsCu(cu, astCtx, mockUriToRealUri, null);
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
            postExecute(rc, modeFlag, listener);

            if (capturedAst[0] != null) {
                if ("--check".equals(modeFlag)) {
                    if (rc == 0) {
                        AST_CACHE.put(uri, capturedCtx[0], capturedAst[0],
                                      api, listener, primaryArg);
                    } else {
                        AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);
                    }
                    cacheSpecsCu(capturedAst[0], capturedCtx[0], mockUriToRealUri, null);
                } else if ("--esc".equals(modeFlag)) {
                    ASTCache.Entry existing = AST_CACHE.get(uri);
                    if (existing == null || !existing.supportsDoEsc()) {
                        AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);
                        cacheSpecsCu(capturedAst[0], capturedCtx[0], mockUriToRealUri, null);
                    }
                }
            }

            Map<String, IProverResult.Kind> proofResults =
                    filterProofResults(methodName, prc != null ? prc.getResults() : Map.of());
            Map<String, List<org.eclipse.lsp4j.Diagnostic>> allDiags =
                    listener.toLspDiagnosticsAll(compiledPathToRealUri);
            List<org.eclipse.lsp4j.Diagnostic> primaryDiags = allDiags.getOrDefault(uri, List.of());
            if ("--check".equals(modeFlag)) {
                int companionFiles = allDiags.size() - 1;
                int companionTotal = allDiags.values().stream().mapToInt(List::size).sum() - primaryDiags.size();
                String companionNote = companionFiles > 0
                        ? " (+" + companionTotal + " diagnostic(s) in " + companionFiles + " companion file(s))"
                        : "";
                log(" --check " + fname + ": " + primaryDiags.size() + " diagnostic(s)" + companionNote);
            } else if (rc == 5) {
                log(" --esc " + fname + " cancelled: " + cancelSummary(proofResults));
            } else {
                log(" --esc " + fname + " complete: " + proofResults.size() + " method(s), " + primaryDiags.size() + " diagnostic(s)");
            }
            return new CheckResult(primaryDiags, rc, proofResults,
                    listener.toForeignMessages(primaryArg), allDiags,
                    prc != null ? prc.getDiagsByMethod() : Map.of());
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
                if (primaryArg == null) return new CheckResult(List.of(), 0, Map.of(), List.of(), Map.of(), Map.of());
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
            if ("--check".equals(modeFlag)) log(" --check " + fname + invocationSuffix(args));
            else log(" --esc " + fname + methodDesc + invocationSuffix(args));

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
                        cacheSpecsCu(cu, astCtx, tempUriToRealUri, tempDirPrefix);
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
            postExecute(rc, modeFlag, listener);

            if (capturedAst[0] != null) {
                if ("--check".equals(modeFlag)) {
                    if (rc == 0) {
                        AST_CACHE.put(uri, capturedCtx[0], capturedAst[0],
                                      api, listener, primaryArg);
                    } else {
                        AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);
                    }
                    cacheSpecsCu(capturedAst[0], capturedCtx[0], tempUriToRealUri, tempDirPrefix);
                } else if ("--esc".equals(modeFlag)) {
                    ASTCache.Entry existing = AST_CACHE.get(uri);
                    if (existing == null || !existing.supportsDoEsc()) {
                        AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);
                        cacheSpecsCu(capturedAst[0], capturedCtx[0], tempUriToRealUri, tempDirPrefix);
                    }
                }
            }

            Map<String, IProverResult.Kind> proofResults =
                    filterProofResults(methodName, prc != null ? prc.getResults() : Map.of());
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
                log(" --check " + fname + ": " + primaryDiags.size() + " diagnostic(s)" + companionNote);
            } else if (rc == 5) {
                log(" --esc " + fname + " cancelled: " + cancelSummary(proofResults));
            } else {
                log(" --esc " + fname + " complete: " + proofResults.size() + " method(s), " + primaryDiags.size() + " diagnostic(s)");
            }
            return new CheckResult(primaryDiags, rc, proofResults,
                    listener.toForeignMessages(primaryArg), allDiags,
                    prc != null ? prc.getDiagsByMethod() : Map.of());
        } catch (IOException e) {
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of(), Map.of());
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
     * When {@code --method} is passed only the targeted method is proved; OpenJML
     * marks every other method as {@code SKIPPED}.  Retain only the entry whose
     * bare name matches the requested method so callers see a single meaningful result.
     */
    private static Map<String, IProverResult.Kind> filterProofResults(
            String methodName, Map<String, IProverResult.Kind> results) {
        if (methodName == null || methodName.isEmpty()) return results;
        String simpleTarget = bareMethodName(methodName);
        return results.entrySet().stream()
                .filter(e -> bareMethodName(e.getKey()).equals(simpleTarget))
                .collect(java.util.stream.Collectors.toMap(
                        Map.Entry::getKey, Map.Entry::getValue,
                        (a, b) -> a, java.util.LinkedHashMap::new));
    }

    /** Single-file run with no open-file context; delegates to {@link #runOnContentWithContext}. */
    private static CheckResult runOnContent(
            String uri, String content, OpenJMLSettings settings, String modeFlag,
            String methodName, boolean collectProofResults,
            BiConsumer<IAPI, Supplier<Integer>> onApiCreated) {
        return runOnContentWithContext(uri, content, Map.of(), settings,
                modeFlag, methodName, collectProofResults, onApiCreated, null, null);
    }

    private static CheckResult runOnFile(
            String filePath, String uri, OpenJMLSettings settings, String modeFlag,
            String methodName, boolean collectProofResults, Consumer<IAPI> onApiReady) {
        return runOnFile(filePath, uri, settings, modeFlag, methodName,
                collectProofResults, onApiReady, null);
    }

    private static CheckResult runOnFile(
            String filePath, String uri, OpenJMLSettings settings, String modeFlag,
            String methodName, boolean collectProofResults, Consumer<IAPI> onApiReady,
            java.util.function.Consumer<JmlMethodDecl> onMethodStarted) {
        return runOnFile(filePath, uri, settings, modeFlag, methodName,
                collectProofResults, onApiReady, onMethodStarted, null);
    }

    private static CheckResult runOnFile(
            String filePath, String uri, OpenJMLSettings settings, String modeFlag,
            String methodName, boolean collectProofResults, Consumer<IAPI> onApiReady,
            java.util.function.Consumer<JmlMethodDecl> onMethodStarted,
            MethodResultCallback onMethodCompleted) {
        var listener = new LspDiagnosticListener();
        if ("--esc".equals(modeFlag)) listener.setSourceTag(DiagnosticConverter.SOURCE_ESC);
        var out = new PrintWriter(System.err, true);
        var api = IAPI.make(out, listener);

        ProofResultCollector prc = null;
        if (collectProofResults) {
            prc = new ProofResultCollector(listener);
            if (onMethodStarted != null) prc.setOnMethodStarted(onMethodStarted);
            if (onMethodCompleted != null) prc.setOnMethodCompleted(onMethodCompleted);
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
        if ("--check".equals(modeFlag)) log(" --check " + fname + invocationSuffix(args));
        else log(" --esc " + fname + methodDesc + invocationSuffix(args));

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
                cacheSpecsCu(cu, ctx, null, null);
            }
        };
        api.setASTListener(astListener);
        int rc;
        try {
            rc = api.execute(args.toArray(new String[0]));
        } finally {
            api.removeASTListener(astListener);
        }
        ServerLog.serverLog("[CheckRunner.runOnFile] exit code " + rc
                + " (" + modeFlag + ")");

        if (capturedAst[0] != null) {
            if ("--check".equals(modeFlag)) {
                if (rc == 0) {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0],
                                  api, listener, filePath);
                } else {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);
                }
                cacheSpecsCu(capturedAst[0], capturedCtx[0], null, null);
            } else if ("--esc".equals(modeFlag)) {
                ASTCache.Entry existing = AST_CACHE.get(uri);
                if (existing == null || !existing.supportsDoEsc()) {
                    AST_CACHE.put(uri, capturedCtx[0], capturedAst[0]);
                    cacheSpecsCu(capturedAst[0], capturedCtx[0], null, null);
                }
            }
        }

        Map<String, IProverResult.Kind> proofResults =
                prc != null ? prc.getResults() : Map.of();
        List<org.eclipse.lsp4j.Diagnostic> diags = listener.toLspDiagnostics(filePath, uri);
        if ("--check".equals(modeFlag))
            log(" --check " + fname + ": " + diags.size() + " diagnostic(s)");
        else if (rc == 5)
            log(" --esc " + fname + " cancelled: " + cancelSummary(proofResults));
        else
            log(" --esc " + fname + " complete: " + proofResults.size() + " method(s), " + diags.size() + " diagnostic(s)");
        for (String msg : listener.toGlobalMessages()) logToolWarning(msg);
        return new CheckResult(diags, rc,
                proofResults, listener.toForeignMessages(filePath),
                listener.toLspDiagnosticsByFile(),
                prc != null ? prc.getDiagsByMethod() : Map.of());
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
            ServerLog.serverLog("[CheckRunner.runDoEscMethod] no cached IAPI for " + uri
                    + " — falling back to fresh engine");
            String filePath = uriToPath(uri);
            if (filePath != null) return runEscFileMethod(filePath, uri, methodName, settings);
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of(), Map.of());
        }

        String simple = simpleName(methodName);
        List<JmlTree.JmlMethodDecl> methods = findMethodsBySimpleName(entry.ast(), simple);
        if (methods.isEmpty()) {
            ServerLog.serverLog("[CheckRunner.runDoEscMethod] method '" + simple
                    + "' not found in cached AST for " + uri + " — falling back to fresh engine");
            String filePath = uriToPath(uri);
            if (filePath != null) return runEscFileMethod(filePath, uri, methodName, settings);
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of(), Map.of());
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
        return new CheckResult(allDiags, exitCode, proofResults, List.of(), Map.of(), Map.of());
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
            ServerLog.serverLog("[CheckRunner.runDoEscFileAsync] no cached IAPI for " + uri
                    + " — falling back to fresh engine");
            String filePath = uriToPath(uri);
            CheckResult result = (filePath != null)
                    ? runEscFile(filePath, uri, settings)
                    : new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of(), Map.of());
            return CompletableFuture.completedFuture(result);
        }

        List<JmlTree.JmlMethodDecl> methods = findAllMethods(entry.ast());
        if (methods.isEmpty()) {
            return CompletableFuture.completedFuture(
                    new CheckResult(List.of(), 0, Map.of(), List.of(), Map.of(), Map.of()));
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
                        if (ex != null) ServerLog.serverLog(
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
                    ServerLog.serverLog("[CheckRunner.runDoEscFileAsync] done, exitCode="
                            + exitCode + " diags=" + allDiags.size() + " uri=" + uri);
                    return new CheckResult(allDiags, exitCode, proofResults, List.of(), Map.of(), Map.of());
                });
    }

    /** Blocking wrapper around {@link #runDoEscFileAsync} (used by tests). */
    public static CheckResult runDoEscFile(String uri, OpenJMLSettings settings) {
        try {
            return runDoEscFileAsync(uri, settings, null).get();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of(), Map.of());
        } catch (ExecutionException e) {
            ServerLog.serverLog("[CheckRunner.runDoEscFile] failed: " + e.getCause());
            return new CheckResult(List.of(), -1, Map.of(), List.of(), Map.of(), Map.of());
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
        ServerLog.serverLog("[CheckRunner.doEscOneMethod] doESC on " + method.name + " in " + uri);
        log(" --esc " + msig + " starting");
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
                        rawDiags, entry.sourcePath(), uri, DiagnosticConverter.SOURCE_ESC);
        IProverResult.Kind kind = result != null ? result.result() : null;
        int exitCode = (kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT) ? 6 : 0;
        ServerLog.serverLog("[CheckRunner.doEscOneMethod] " + method.name
                + " -> " + kind + ", exitCode=" + exitCode);
        log(" --esc " + msig + ": " + kindLabel(kind));
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

    private static List<String> buildArgs(OpenJMLSettings settings, String modeFlag) {
        return buildArgs(settings, modeFlag, null);
    }

    private static List<String> buildArgs(OpenJMLSettings settings, String modeFlag, Path prefixDir) {
        List<String> args = new ArrayList<>();

        // Project-independent tool options (--properties, warning flags, etc.) first.
        if (settings.clientSettings.toolOptions != null && !settings.clientSettings.toolOptions.isEmpty())
            args.addAll(settings.clientSettings.toolOptions);

        args.add(modeFlag);
        if (settings.specsPath != null && !settings.specsPath.isBlank()) {
            args.add("--specs-path");
            args.add(settings.specsPath);
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
     *   <li>{@link OpenJMLSettings#rootPaths} — per-project root paths, or
     *       {@link OpenJMLSettings#effectiveRoots()} as fallback</li>
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
            // Do NOT also add rootPaths — for default-package files that would
            // introduce a duplicate class source alongside the temp dir,
            // causing javac to silently suppress diagnostics.
            parts.add(settings.sourcePath);
        } else {
            // No explicit source path: fall back to per-project rootPaths or effective roots.
            if (settings.rootPaths != null && !settings.rootPaths.isEmpty()) {
                parts.add(String.join(java.io.File.pathSeparator, settings.rootPaths));
            } else {
                List<String> roots = settings.effectiveRoots();
                if (!roots.isEmpty())
                    parts.add(String.join(java.io.File.pathSeparator, roots));
            }
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
        if (settings.specsPath == null || settings.specsPath.isBlank()) return "";
        List<String> parts = new ArrayList<>();
        if (prefixDir != null) parts.add(prefixDir.toString());
        // Do NOT add rootPaths here — project roots are not spec roots.
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
        ServerLog.serverLog(sb.toString());
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
