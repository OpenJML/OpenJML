package org.openjml.lsp;

import org.eclipse.lsp4j.CodeLens;
import org.eclipse.lsp4j.CodeLensParams;
import org.eclipse.lsp4j.Command;
import org.eclipse.lsp4j.CompletionItem;
import org.eclipse.lsp4j.CompletionList;
import org.eclipse.lsp4j.CompletionParams;
import org.eclipse.lsp4j.DocumentHighlight;
import org.eclipse.lsp4j.DocumentHighlightParams;
import org.eclipse.lsp4j.DocumentSymbol;
import org.eclipse.lsp4j.DocumentSymbolParams;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.SymbolKind;
import org.eclipse.lsp4j.DeclarationParams;
import org.eclipse.lsp4j.DefinitionParams;
import org.eclipse.lsp4j.ReferenceParams;
import org.eclipse.lsp4j.RenameParams;
import org.eclipse.lsp4j.WorkspaceEdit;
import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.jsonrpc.ResponseErrorException;
import org.eclipse.lsp4j.DidChangeTextDocumentParams;
import org.eclipse.lsp4j.DidCloseTextDocumentParams;
import org.eclipse.lsp4j.DidOpenTextDocumentParams;
import org.eclipse.lsp4j.DidSaveTextDocumentParams;
import org.eclipse.lsp4j.Hover;
import org.eclipse.lsp4j.HoverParams;
import org.eclipse.lsp4j.SignatureHelp;
import org.eclipse.lsp4j.SignatureHelpParams;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.LocationLink;
import org.eclipse.lsp4j.MarkupContent;
import org.eclipse.lsp4j.MarkupKind;
import org.eclipse.lsp4j.MessageActionItem;
import org.eclipse.lsp4j.MessageParams;
import org.eclipse.lsp4j.MessageType;
import org.eclipse.lsp4j.ShowMessageRequestParams;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.PrepareRenameDefaultBehavior;
import org.eclipse.lsp4j.PrepareRenameParams;
import org.eclipse.lsp4j.PrepareRenameResult;
import org.eclipse.lsp4j.PublishDiagnosticsParams;
import org.eclipse.lsp4j.FileChangeType;
import org.eclipse.lsp4j.FoldingRange;
import org.eclipse.lsp4j.FoldingRangeRequestParams;
import org.eclipse.lsp4j.InlayHint;
import org.eclipse.lsp4j.InlayHintParams;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.jsonrpc.messages.Either3;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.openjml.IAPI;
import org.openjml.IProverResult;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Consumer;
import java.util.function.Supplier;

/**
 * Handles text document lifecycle notifications.
 *
 * <p>Two independent checks are run per document: a fast {@code --check} pass
 * and a slower {@code --esc} pass.  Each has its own trigger setting and its
 * own debounce delay.  Their diagnostics are merged before publishing so that
 * neither pass's results overwrite the other's.
 *
 * <p><b>--check trigger</b> ({@link OpenJMLSettings#checkTriggerOn}):
 * <ul>
 *   <li>{@code "edit"} (default) — check on open and every change (debounced {@value #CHECK_DEBOUNCE_MS} ms)</li>
 *   <li>{@code "save"} — check on open and save only</li>
 * </ul>
 * In both modes check always runs on open and save.
 *
 * <p><b>--esc trigger</b> ({@link OpenJMLSettings#escTriggerOn}):
 * <ul>
 *   <li>{@code "manual"} (default) — only on explicit {@code openjml.runEsc} command</li>
 *   <li>{@code "save"} — on every save</li>
 *   <li>{@code "edit"} — on every change (debounced {@value #ESC_DEBOUNCE_MS} ms; expensive)</li>
 * </ul>
 * ESC is never triggered automatically on open — only on save, edit (per the setting),
 * or the explicit {@code openjml.runEsc} command.
 *
 * <p>Multiple ESC operations may run concurrently on different files.  Within
 * a single file, starting a new ESC cancels the previous one (via
 * {@link Future#cancel(boolean)}) and a generation counter ensures stale
 * results are silently discarded when they arrive late.
 *
 * <p>Text document sync mode is {@code Full}.
 */
public class OpenJMLTextDocumentService implements TextDocumentService {

    /** Debounce delay for --check in edit mode. */
    static final long CHECK_DEBOUNCE_MS = 500;

    /** Debounce delay for --esc in edit mode (longer — ESC is expensive). */
    static final long ESC_DEBOUNCE_MS = 2000;

    // --- ESC status per method (for code lens) ---

    enum EscResult { UNKNOWN, CHECKING, VERIFIED, INFEASIBLE, NOT_VERIFIED, SKIPPED, TIMEOUT, CANCELLED, CHECK_ERROR, CHECK_ERROR_DEPS }

    record MethodStatus(EscResult result, int issueCount) {
        static final MethodStatus UNKNOWN      = new MethodStatus(EscResult.UNKNOWN,      0);
        static final MethodStatus CHECKING     = new MethodStatus(EscResult.CHECKING,     0);
        static final MethodStatus VERIFIED     = new MethodStatus(EscResult.VERIFIED,     0);
        static final MethodStatus INFEASIBLE   = new MethodStatus(EscResult.INFEASIBLE,   0);
        static final MethodStatus SKIPPED      = new MethodStatus(EscResult.SKIPPED,      0);
        static final MethodStatus TIMEOUT      = new MethodStatus(EscResult.TIMEOUT,      0);
        static final MethodStatus CANCELLED    = new MethodStatus(EscResult.CANCELLED,    0);
        static final MethodStatus CHECK_ERROR       = new MethodStatus(EscResult.CHECK_ERROR,       0);
        static final MethodStatus CHECK_ERROR_DEPS  = new MethodStatus(EscResult.CHECK_ERROR_DEPS,  0);
        static MethodStatus notVerified(int n) { return new MethodStatus(EscResult.NOT_VERIFIED, n); }
        static MethodStatus done(int n) {
            return n == 0 ? VERIFIED : notVerified(n);
        }

        String label() {
            return switch (result) {
                case UNKNOWN      -> "OpenJML: \u2014  \u25b6 Run ESC";                  // — ▶
                case CHECKING     -> "OpenJML: \u29d7 Checking\u2026  \u2715 Cancel";    // ⧗ … ✕
                case VERIFIED     -> "OpenJML: \u2713 Verified  \u21ba Re-run";          // ✓ ↺
                case INFEASIBLE   -> "OpenJML: Infeasible  \u21ba Re-run";
                case NOT_VERIFIED -> "OpenJML: \u2717 Not verified"                      // ✗
                        + (issueCount > 0 ? " (" + issueCount + " issue(s))" : "")
                        + "  \u21ba Re-run";
                case SKIPPED      -> "OpenJML: Skipped  \u25b6 Run ESC";
                case TIMEOUT      -> "OpenJML: Timeout  \u21ba Re-run";
                case CANCELLED    -> "OpenJML: Cancelled  \u25b6 Run ESC";
                case CHECK_ERROR       -> "OpenJML: Check error  \u21ba Re-run";
                case CHECK_ERROR_DEPS  -> "OpenJML: Check error in other files  \u21ba Re-run";
            };
        }
    }

    private final OpenJMLSettings globalSettings;
    private final String codeLensCommand;
    private LanguageClient client;

    private final ExecutorService          executor      = Executors.newCachedThreadPool();
    private final ScheduledExecutorService scheduler     = Executors.newSingleThreadScheduledExecutor();

    /** Pending debounce futures for --check, keyed by URI. */
    private final Map<String, ScheduledFuture<?>> pendingCheck = new ConcurrentHashMap<>();

    /** Pending debounce future for scheduleCheckForPaths (path-based manual check). */
    private volatile ScheduledFuture<?> pendingCheckPaths;

    /** Pending debounce futures for --esc, keyed by URI. */
    private final Map<String, ScheduledFuture<?>> pendingEsc   = new ConcurrentHashMap<>();

    /** Latest --check diagnostics per URI. */
    private final Map<String, List<Diagnostic>> checkDiags = new ConcurrentHashMap<>();

    /** Latest --esc diagnostics per URI. */
    private final Map<String, List<Diagnostic>> escDiags   = new ConcurrentHashMap<>();

    /** Latest --rac diagnostics per URI (kept separate so check diags are not overwritten). */
    private final Map<String, List<Diagnostic>> racDiags   = new ConcurrentHashMap<>();

    /** Per-URI generation counter: incremented on each new ESC submission. */
    private final Map<String, AtomicLong> escGen = new ConcurrentHashMap<>();

    /** Currently running ESC Future per URI (for cancellation). */
    private final Map<String, Future<?>> runningEscTasks = new ConcurrentHashMap<>();

    /**
     * IAPI instance for the actively-executing ESC subprocess, per URI.
     * Populated by the {@code onApiReady} hook in {@link #submitEsc} once the
     * fresh IAPI has been created; removed when the task completes or is cancelled.
     * Used by {@link #abortEscForUri} to kill the underlying z3 process immediately.
     */
    private final Map<String, IAPI> runningEscApis = new ConcurrentHashMap<>();

    /**
     * Currently running per-method ESC Future, keyed by {@code "uri#methodName"}.
     * Parallel to {@link #runningEscTasks} but for single-method runs.
     * Multiple per-method runs on the same file run concurrently without cancelling
     * each other or the whole-file run.
     */
    private final Map<String, Future<?>> runningEscMethodTasks = new ConcurrentHashMap<>();

    /**
     * IAPI instance for the actively-executing per-method ESC subprocess,
     * keyed by {@code "uri#methodName"}.
     */
    private final Map<String, IAPI> runningEscMethodApis = new ConcurrentHashMap<>();

    /** Per-method ESC status, keyed by URI then method start line. */
    private final Map<String, Map<Integer, MethodStatus>> methodEscStatus = new ConcurrentHashMap<>();

    /**
     * Last-seen source content per URI, populated by {@link #didOpen} and
     * {@link #didChange} and updated by {@link #rename} (see below).
     *
     * <p><b>LSP4E / Eclipse tracking note</b>: LSP4E only sends
     * {@code textDocument/didOpen} for the <em>active</em> editor.  Files that
     * are open in non-active editor tabs are <em>not</em> registered with the
     * LSP client and therefore never appear in this map.  Concretely:
     * <ul>
     *   <li>A.java (the editor the user renamed from) is in this map — it was
     *       active when the user initiated the rename.</li>
     *   <li>A.jml (open in a non-active Generic Editor tab) is <em>not</em> in
     *       this map even while the file is on screen.</li>
     *   <li>B.java (not open at all) is not in this map.</li>
     * </ul>
     * This is normal and intentional: the LSP protocol does not require clients
     * to send {@code didOpen} for every file they display.  The server must be
     * prepared to handle files that are in the workspace but absent from this map.
     *
     * <p>For {@code --check} this is fine: absent files are read from disk, and
     * disk content matches the editor content for non-dirty files.  For rename,
     * the server proactively patches this map with the post-rename content for
     * any entry that already exists (see {@link #rename}), because Eclipse does
     * not send {@code textDocument/didChange} after applying a server-initiated
     * {@code WorkspaceEdit}.
     */
    private final Map<String, String> lastContent = new ConcurrentHashMap<>();

    /**
     * URIs that have been modified since their last save (or since {@code didOpen}).
     *
     * <p>Updated by {@link #didChange} (add), {@link #didSave} (remove), and
     * {@link #didClose} (remove).  Used to filter {@link #lastContent} when building
     * the mock-file snapshot passed to OpenJML: only truly dirty files need to be
     * mocked; clean files are read from disk with identical content.
     */
    private final java.util.Set<String> dirtyUris = ConcurrentHashMap.newKeySet();

    /** Content (by identity hash) of the last successfully submitted --check, per URI. */
    private final Map<String, String> lastCheckedContent = new ConcurrentHashMap<>();

    /**
     * URIs for which the client currently holds at least one OpenJML diagnostic marker.
     *
     * <p>Updated by {@link #publishDiags}: added when a non-empty list is published,
     * removed when an empty list (clear) is published.  This is the authoritative set
     * used by {@link #clearMarkers} so that markers on dependency files (companions from
     * cross-file checks, or files from a {@code --dirs} run) are not left behind.
     */
    private final java.util.Set<String> markedUris = ConcurrentHashMap.newKeySet();

    /**
     * The most recently submitted --check future (per URI).  Set just before
     * the check task is submitted to the executor; completed when the check
     * finishes.  {@link #documentSymbol} chains off this so it can return
     * populated symbols even when the outline is requested before the first
     * check completes.
     */
    private final Map<String, CompletableFuture<Void>> lastCheckFuture = new ConcurrentHashMap<>();

    /**
     * Set to {@code true} when any open document is edited ({@link #didChange}).
     * Cleared after a project-wide {@code --check} pass completes.  Navigation
     * operations ({@code definition}, {@code declaration}, {@code references},
     * {@code rename}) trigger a fresh project-wide check when this flag is set,
     * ensuring all files share a single IAPI compilation context so that
     * cross-file symbol identity holds.
     *
     * <p>Focus changes and saves do NOT set this flag: they do not alter
     * in-memory content and therefore cannot invalidate the nav context.
     */
    private volatile boolean navCacheDirty = true;

    /**
     * @param globalSettings  shared settings object
     * @param codeLensCommand the command name to embed in code-lens actions (e.g. run ESC for method)
     */
    public OpenJMLTextDocumentService(OpenJMLSettings globalSettings, String codeLensCommand) {
        this.globalSettings = globalSettings;
        this.codeLensCommand = codeLensCommand;
    }

    public void connect(LanguageClient client) {
        this.client = client;
        CheckRunner.setLogCallback(msg -> {
            if (client != null)
                client.logMessage(new MessageParams(MessageType.Log, msg));
        });
    }

    /**
     * Returns a snapshot of {@link #lastContent} filtered to only dirty files.
     *
     * <p>Only files whose URIs are in {@link #dirtyUris} (i.e. modified since
     * their last save) are included.  Clean files are read from disk by OpenJML
     * directly — their in-memory and on-disk content are identical, so no mock
     * is needed and including them would only add noise to the OpenJML console
     * output (showing skipped methods in every open clean file).
     *
     * <p>The snapshot is taken atomically at call time so that background ESC
     * threads see a consistent view even if the user continues editing.
     */
    private Map<String, String> dirtySnapshot() {
        Map<String, String> result = new java.util.HashMap<>();
        for (String uri : dirtyUris) {
            String content = lastContent.get(uri);
            if (content != null) result.put(uri, content);
        }
        return java.util.Collections.unmodifiableMap(result);
    }

    @Override
    public void didOpen(DidOpenTextDocumentParams params) {
        String uri     = params.getTextDocument().getUri();
        String content = params.getTextDocument().getText();
        System.err.println("[didOpen] uri=" + uri);
        lastContent.put(uri, content);

        // Notify the client to re-query code lenses now that lastContent is populated.
        // This ensures the initial "—" status appears even before the first --check.
        refreshCodeLenses();

        // --check: always on open
        scheduleCheckNow(uri, content);
        // ESC is never triggered on open — only on save/edit (per trigger setting)
        // or the explicit openjml.runEsc command.
    }

    @Override
    public void didChange(DidChangeTextDocumentParams params) {
        if (params.getContentChanges().isEmpty()) return;
        String uri     = params.getTextDocument().getUri();
        System.err.println("[didChange] uri=" + uri);
        String content = globalSettings.incrementalSync
                ? IncrementalSyncApplier.apply(lastContent.get(uri),
                                               params.getContentChanges())
                : params.getContentChanges().get(0).getText();
        lastContent.put(uri, content);
        dirtyUris.add(uri);
        // Mark nav cache dirty: the next navigation will trigger a project-wide check.
        navCacheDirty = true;
        // Invalidate cached check state for all other open files so that focus-triggered
        // rechecks pick up this change in their cross-file context.  When the primary
        // check completes, companion files that were actually compiled will be re-marked
        // as up-to-date, so only truly-uncompiled files will be rechecked on focus.
        lastCheckedContent.keySet().removeIf(k -> !k.equals(uri));

        // --check: debounced if in edit mode
        if (globalSettings.isCheckOnEdit()) {
            if (uri.endsWith(".jml")) {
                // .jml files are spec files; redirect check to companion .java.
                // The dirty .jml content is already in lastContent so checkWithContext
                // will use it when writing the temp directory.
                String javaUri = resolveCompanionJavaUri(uri, content);
                if (javaUri != null) {
                    final String fJavaUri = javaUri;
                    debounce(pendingCheck, fJavaUri,
                            () -> { String jc = lastContent.get(fJavaUri);
                                    if (jc != null) runCheckContent(fJavaUri, jc); },
                            CHECK_DEBOUNCE_MS);
                }
            } else {
                debounce(pendingCheck, uri,
                        () -> runCheckContent(uri, content),
                        CHECK_DEBOUNCE_MS);
            }
        }

        // --esc: debounced if in edit mode
        if (globalSettings.isEscOnEdit()) {
            debounce(pendingEsc, uri,
                    () -> startEscContent(uri, content),
                    ESC_DEBOUNCE_MS);
        }
    }

    @Override
    public void didSave(DidSaveTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        dirtyUris.remove(uri);
        cancelPending(uri);

        // --check: always on save.
        // ESC on save is handled by the VS Code extension (onDidSaveTextDocument),
        // which can distinguish manual saves from auto-saves.  The server never
        // triggers ESC from didSave.
        scheduleCheckFile(uri);
    }

    @Override
    public void didClose(DidCloseTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        dirtyUris.remove(uri);
        cancelPending(uri);
        checkDiags.remove(uri);
        escDiags.remove(uri);
        racDiags.remove(uri);
        lastContent.remove(uri);
        methodEscStatus.remove(uri);
        CheckRunner.getASTCache().remove(uri);
        publishDiags(uri, List.of());
    }

    // --- code lens ---

    @Override
    public CompletableFuture<List<? extends CodeLens>> codeLens(CodeLensParams params) {
        String uri = params.getTextDocument().getUri();
        String content = lastContent.get(uri);
        if (content == null) {
            // didOpen may not have arrived yet; fall back to reading from disk so that
            // initial UNKNOWN-status lenses are returned rather than an empty list.
            try { content = java.nio.file.Files.readString(
                      java.nio.file.Path.of(new java.net.URI(uri))); }
            catch (Exception ignored) {}
        }
        if (content == null) return CompletableFuture.completedFuture(List.of());

        ASTCache.Entry astEntry = CheckRunner.getASTCache().get(uri);
        List<JavaSourceScanner.MethodInfo> methods = (astEntry != null)
                ? JavaSourceScanner.findMethodsFromAst(astEntry.ast(), content)
                : JavaSourceScanner.findMethods(content);
        Map<Integer, MethodStatus> statuses = methodEscStatus.getOrDefault(uri, Map.of());

        List<CodeLens> lenses = new ArrayList<>(methods.size());
        for (JavaSourceScanner.MethodInfo m : methods) {
            MethodStatus s = statuses.getOrDefault(m.startLine(), MethodStatus.UNKNOWN);
            var range = new Range(new Position(m.startLine(), 0),
                                  new Position(m.startLine(), 0));
            // Method reference encodes both name and start line so overloads are
            // distinguished and the server can locate the exact method on the next request.
            // The command is always RUN_ESC_FOR_METHOD regardless of state: when the
            // method is currently CHECKING, scheduleEscForMethod cancels the in-flight
            // run instead of starting a new one.  Using a single command avoids VS Code
            // treating a command change as a new lens and showing duplicates.
            String methodRef = m.name() + "@" + m.startLine();
            lenses.add(new CodeLens(range,
                    new Command(s.label(), OpenJMLCommands.RUN_ESC_FOR_METHOD,
                                List.<Object>of(uri, methodRef)),
                    null));
        }
        return CompletableFuture.completedFuture(lenses);
    }

    // --- hover ---

    @Override
    public CompletableFuture<Either<List<CompletionItem>, CompletionList>> completion(
            CompletionParams params) {
        String uri     = params.getTextDocument().getUri();
        String content = lastContent.get(uri);
        if (content == null) return CompletableFuture.completedFuture(Either.forLeft(List.of()));
        List<CompletionItem> items =
                JmlCompletionProvider.complete(content, params.getPosition());
        return CompletableFuture.completedFuture(Either.forLeft(items));
    }

    private List<Either<SymbolInformation, DocumentSymbol>> buildSymbolResult(
            String uri, ASTCache.Entry entry, String content) {
        boolean jmlOnly = !Boolean.TRUE.equals(globalSettings.useIntegratedOutline);
        List<DocumentSymbol> symbols = DocumentSymbolProvider.fromAst(entry.ast(), content, jmlOnly);
        List<Either<SymbolInformation, DocumentSymbol>> result = new ArrayList<>(symbols.size());
        for (DocumentSymbol ds : symbols) result.add(Either.forRight(ds));
        return result;
    }

    @Override
    public CompletableFuture<List<Either<SymbolInformation, DocumentSymbol>>> documentSymbol(
            DocumentSymbolParams params) {
        String uri     = params.getTextDocument().getUri();
        String content = lastContent.get(uri);
        if (content == null) {
            return CompletableFuture.completedFuture(List.of());
        }
        // .jml spec files redirect their check to the companion .java; look up under that URI.
        String cacheUri = uri.endsWith(".jml")
                ? uri.substring(0, uri.length() - 4) + ".java"
                : uri;
        // If a check is in flight (first open OR edit), wait for it so the
        // outline reflects the current source rather than the previous AST.
        CompletableFuture<Void> pending = lastCheckFuture.get(cacheUri);
        if (pending != null && !pending.isDone()) {
            final String finalContent = content;
            return pending.thenApply(_v -> {
                ASTCache.Entry e2 = CheckRunner.getASTCache().get(cacheUri);
                if (e2 == null) return List.<Either<SymbolInformation, DocumentSymbol>>of();
                return buildSymbolResult(uri, e2, finalContent);
            });
        }
        ASTCache.Entry entry = CheckRunner.getASTCache().get(cacheUri);
        if (entry == null) {
            return CompletableFuture.completedFuture(List.of());
        }
        List<Either<SymbolInformation, DocumentSymbol>> result = buildSymbolResult(uri, entry, content);
        return CompletableFuture.completedFuture(result);
    }

    @Override
    public CompletableFuture<List<FoldingRange>> foldingRange(FoldingRangeRequestParams params) {
        String uri     = params.getTextDocument().getUri();
        String content = lastContent.get(uri);
        if (content == null) {
            // Not yet in memory (request arrived before didOpen) — read from disk.
            String path = CheckRunner.uriToPath(uri);
            if (path == null) return CompletableFuture.completedFuture(List.of());
            try {
                content = java.nio.file.Files.readString(java.nio.file.Path.of(path));
            } catch (java.io.IOException e) {
                return CompletableFuture.completedFuture(List.of());
            }
        }
        return CompletableFuture.completedFuture(FoldingRangeProvider.fromSource(content));
    }

    @Override
    public CompletableFuture<Hover> hover(HoverParams params) {
        String uri = params.getTextDocument().getUri();
        String content = lastContent.get(uri);
        if (content == null) return CompletableFuture.completedFuture(null);

        int line = params.getPosition().getLine();
        int col  = params.getPosition().getCharacter();

        // If the cursor is on a var-declared variable, return its inferred type.
        String varType = InlayHintProvider.findVarTypeAtPosition(
                uri, content, line, col, CheckRunner.getASTCache());
        if (varType != null) {
            var hover = new Hover(new MarkupContent(MarkupKind.PLAINTEXT, varType));
            return CompletableFuture.completedFuture(hover);
        }

        // Otherwise show the JML spec of the enclosing method.
        List<JavaSourceScanner.MethodInfo> methods = JavaSourceScanner.findMethods(content);
        JavaSourceScanner.MethodInfo method = null;
        for (JavaSourceScanner.MethodInfo m : methods) {
            if (line >= m.startLine() && line <= m.endLine()) {
                method = m;
                break;
            }
        }
        if (method == null) return CompletableFuture.completedFuture(null);

        String spec = extractJmlSpec(content, method.startLine());
        if (spec.isBlank()) return CompletableFuture.completedFuture(null);

        var hover = new Hover(new MarkupContent(MarkupKind.MARKDOWN,
                "**JML spec for `" + method.name() + "`**\n```java\n" + spec + "\n```"));
        return CompletableFuture.completedFuture(hover);
    }

    // --- signature help ---

    @Override
    public CompletableFuture<SignatureHelp> signatureHelp(SignatureHelpParams params) {
        String uri     = params.getTextDocument().getUri();
        String content = lastContent.get(uri);
        return CompletableFuture.completedFuture(
                SignatureHelpProvider.compute(params, content, CheckRunner.getASTCache()));
    }

    // --- inlay hints ---

    @Override
    public CompletableFuture<List<InlayHint>> inlayHint(InlayHintParams params) {
        String uri     = params.getTextDocument().getUri();
        String content = lastContent.get(uri);
        if (content == null) return CompletableFuture.completedFuture(List.of());
        return CompletableFuture.completedFuture(
                InlayHintProvider.compute(params, content, CheckRunner.getASTCache(),
                        globalSettings.isJmlOnly()));
    }

    // --- go to definition ---

    /**
     * Resolve the declaration of the identifier under the cursor.
     *
     * <p>Works for identifiers in both regular Java code and JML clauses
     * ({@code //@ requires}, {@code //@ ensures}, etc.).  The AST must have
     * been cached by a prior {@code --check} run for the same URI.
     */
    @Override
    public CompletableFuture<Either<List<? extends Location>, List<? extends LocationLink>>>
            definition(DefinitionParams params) {
        String uri = params.getTextDocument().getUri();
        String source = lastContent.get(uri);
        if (source == null)
            return CompletableFuture.completedFuture(Either.forLeft(List.of()));

        return ensureNavCacheReady().thenCompose(v -> {
            ASTCache cache = CheckRunner.getASTCache();
            boolean hasAst = cache.get(uri) != null;
            System.err.println("[OpenJML] definition: uri=" + uri
                    + "  hasContent=true  hasAST=" + hasAst);

            // For .jml spec files: if the .jml AST is cached directly (via cacheSpecsCu),
            // use it directly (normal path below).  If not yet cached, redirect lookup to
            // the companion .java AST (which has specsCompilationUnit pointing to the .jml
            // AST), using .jml source for cursor-offset computation.
            if (uri.endsWith(".jml") && !hasAst) {
                String javaUri = resolveCompanionJavaUri(uri, source);
                if (javaUri != null) {
                    String jmlSource = source;
                    CompletableFuture<Void> pending = lastCheckFuture.get(javaUri);
                    CompletableFuture<Void> ready = (pending != null && !pending.isDone())
                            ? pending : CompletableFuture.completedFuture(null);
                    return ready.thenApply(v2 -> {
                        ASTCache.Entry entry = cache.get(javaUri);
                        if (entry == null) {
                            System.err.println("[OpenJML] definition: no AST for " + javaUri);
                            return Either.<List<? extends Location>, List<? extends LocationLink>>
                                    forLeft(List.of());
                        }
                        System.err.println("[OpenJML] definition: redirecting to java AST " + javaUri);
                        Map<String, String> synthetic = new java.util.HashMap<>(lastContent);
                        synthetic.put(javaUri, jmlSource);
                        Location loc = DefinitionFinder.findDefinition(
                                javaUri,
                                params.getPosition().getLine(),
                                params.getPosition().getCharacter(),
                                synthetic,
                                cache);
                        System.err.println("[OpenJML] definition result (jml): " + loc);
                        List<Location> res = loc != null ? List.of(loc) : List.of();
                        return Either.<List<? extends Location>, List<? extends LocationLink>>
                                forLeft(res);
                    });
                }
            }

            Location loc = DefinitionFinder.findDefinition(
                    uri,
                    params.getPosition().getLine(),
                    params.getPosition().getCharacter(),
                    lastContent,
                    cache);

            System.err.println("[OpenJML] definition result: " + loc);
            List<Location> result = loc != null ? List.of(loc) : List.of();
            return CompletableFuture.completedFuture(Either.forLeft(result));
        });
    }

    // --- find references ---

    /**
     * Find all references to the symbol under the cursor.
     *
     * <p>Searches every AST currently in the cache.  Symbol identity ({@code ==})
     * is used to match references, which is correct within a single IAPI compilation
     * context.
     *
     * <p>Optimisation opportunity (not yet applied): scope analysis via
     * {@code Symbol.owner} could restrict the search to the relevant file(s)
     * (e.g., private members need only be searched in their declaring class's file).
     */
    @Override
    public CompletableFuture<List<? extends Location>> references(ReferenceParams params) {
        String uri = params.getTextDocument().getUri();
        if (lastContent.get(uri) == null)
            return CompletableFuture.completedFuture(List.of());

        boolean includeDecl = params.getContext() != null
                && params.getContext().isIncludeDeclaration();

        return ensureFreshAndConfirm(uri, "Find References").thenApply(proceed -> {
            if (!proceed) return List.of();
            return ReferenceFinder.findReferences(
                    uri,
                    params.getPosition().getLine(),
                    params.getPosition().getCharacter(),
                    lastContent,
                    CheckRunner.getASTCache(),
                    includeDecl);
        });
    }

    // --- document highlight ---

    /**
     * Return all occurrences of the identifier token under the cursor within the
     * current document.
     *
     * <p>Matching is by <em>name</em>, not by compiler symbol: all AST nodes whose
     * {@code name} field equals the cursor token are reported, regardless of scope.
     * See {@link DocumentHighlightProvider} for the full rationale.
     *
     * <p>For {@code .jml} files the companion {@code .java} URI is resolved and used to
     * locate the specs compilation unit in the AST cache.
     */
    @Override
    public CompletableFuture<List<? extends DocumentHighlight>> documentHighlight(
            DocumentHighlightParams params) {
        String uri = params.getTextDocument().getUri();
        String source = lastContent.get(uri);
        if (source == null) return CompletableFuture.completedFuture(List.of());

        int line = params.getPosition().getLine();
        int col  = params.getPosition().getCharacter();

        return ensureNavCacheReady().thenApply(v -> {
            ASTCache cache = CheckRunner.getASTCache();
            // For .jml files, compute the companion .java URI as a fallback in case the
            // specs CU has not yet been stored under the .jml URI in the live cache.
            // DocumentHighlightProvider tries the .jml URI first and falls back to this.
            String companionJavaUri = uri.endsWith(".jml")
                    ? resolveCompanionJavaUri(uri, source) : null;
            return DocumentHighlightProvider.findHighlights(
                    uri, line, col, lastContent, cache, companionJavaUri);
        });
    }

    // --- go to declaration ---

    /**
     * Resolve the declaration of the identifier under the cursor.
     *
     * <p>For Java and JML identifiers the declaration and definition are the same
     * location (the {@code JCVariableDecl} / {@code JCMethodDecl} node).  This
     * method therefore delegates to the same {@link DefinitionFinder} as
     * {@link #definition}.
     */
    @Override
    public CompletableFuture<Either<List<? extends Location>, List<? extends LocationLink>>>
            declaration(DeclarationParams params) {
        String uri = params.getTextDocument().getUri();
        String source = lastContent.get(uri);
        if (source == null)
            return CompletableFuture.completedFuture(Either.forLeft(List.of()));

        return ensureNavCacheReady().thenCompose(v -> {
            ASTCache cache = CheckRunner.getASTCache();
            if (uri.endsWith(".jml") && cache.get(uri) == null) {
                String javaUri = resolveCompanionJavaUri(uri, source);
                if (javaUri != null) {
                    String jmlSource = source;
                    CompletableFuture<Void> pending = lastCheckFuture.get(javaUri);
                    CompletableFuture<Void> ready = (pending != null && !pending.isDone())
                            ? pending : CompletableFuture.completedFuture(null);
                    return ready.thenApply(v2 -> {
                        ASTCache.Entry entry = cache.get(javaUri);
                        if (entry == null)
                            return Either.<List<? extends Location>, List<? extends LocationLink>>
                                    forLeft(List.of());
                        Map<String, String> synthetic = new java.util.HashMap<>(lastContent);
                        synthetic.put(javaUri, jmlSource);
                        Location loc = DefinitionFinder.findDefinition(
                                javaUri,
                                params.getPosition().getLine(),
                                params.getPosition().getCharacter(),
                                synthetic,
                                cache);
                        List<Location> res = loc != null ? List.of(loc) : List.of();
                        return Either.<List<? extends Location>, List<? extends LocationLink>>
                                forLeft(res);
                    });
                }
            }

            Location loc = DefinitionFinder.findDefinition(
                    uri,
                    params.getPosition().getLine(),
                    params.getPosition().getCharacter(),
                    lastContent,
                    cache);

            List<Location> result = loc != null ? List.of(loc) : List.of();
            return CompletableFuture.completedFuture(Either.forLeft(result));
        });
    }

    // --- prepareRename / rename ---

    /**
     * Validate that a rename is possible at the cursor position.
     *
     * <p>Returns {@code defaultBehavior=true} (let the client infer the rename
     * range from the identifier word) whenever the cursor sits on a valid Java
     * identifier character, so that VS Code prefers our rename provider over
     * other competing providers (e.g. the Red Hat Java extension) for positions
     * inside JML annotations.
     */
    @Override
    public CompletableFuture<Either3<Range, PrepareRenameResult, PrepareRenameDefaultBehavior>>
            prepareRename(PrepareRenameParams params) {
        String uri    = params.getTextDocument().getUri();
        String source = lastContent.get(uri);
        if (source != null) {
            int offset = DefinitionFinder.lineColToOffset(
                    source, params.getPosition().getLine(), params.getPosition().getCharacter());
            if (offset >= 0 && offset < source.length()) {
                char ch = source.charAt(offset);
                if (Character.isJavaIdentifierPart(ch) && !Character.isDigit(ch)
                        || (offset > 0 && Character.isJavaIdentifierPart(source.charAt(offset - 1)))) {
                    // Cursor is on or just after an identifier — signal that rename is supported.
                    return CompletableFuture.completedFuture(
                            Either3.forThird(new PrepareRenameDefaultBehavior(true)));
                }
            }
        }
        return CompletableFuture.failedFuture(
                new Exception("No renameable symbol at this position"));
    }

    /**
     * Rename the symbol under the cursor to {@code params.getNewName()}.
     *
     * <p>Delegates to {@link Renamer#rename}, which validates the new name,
     * finds all references, applies the edits in memory, validates the result
     * with a {@code --check} pass, and returns a {@link WorkspaceEdit}.
     *
     * <p>If the rename would introduce errors or the new name is invalid a
     * {@link ResponseErrorException} is propagated as a failed future so that
     * the LSP client receives a proper JSON-RPC error response.
     *
     * <p><b>WorkspaceEdit application — responsibility split</b>:
     * The server returns a {@link WorkspaceEdit}; the <em>client</em> is
     * responsible for applying it.  In the Eclipse plugin,
     * {@code JmlRenameHandler.applyWorkspaceEditPreservingDirty} handles this:
     * <ul>
     *   <li>Files already open in any editor (active <em>or</em> non-active) —
     *       edits are applied directly to the editor's live {@code IDocument}
     *       buffer, marking the editor dirty.</li>
     *   <li>Files not open in any editor — edits are written to disk via
     *       {@code IFile.setContents} without opening a new editor window,
     *       matching JDT refactoring behaviour.</li>
     * </ul>
     * The plugin does <em>not</em> delegate to
     * {@code LSPEclipseUtils.applyWorkspaceEdit} because LSP4E only tracks
     * documents for which it has sent {@code textDocument/didOpen} (i.e. the
     * active editor); it would write non-active open editors to disk and may
     * open unexpected new editor windows for closed files.
     *
     * <p><b>Server-side lastContent patch</b>:
     * After computing the edit, the server immediately applies the same edits
     * to any entries already in {@link #lastContent}.  Eclipse does not send
     * {@code textDocument/didChange} after applying a server-initiated
     * {@code WorkspaceEdit}, so without this patch the server's in-memory
     * snapshot would be stale for the next navigation or check operation.
     */
    @Override
    public CompletableFuture<WorkspaceEdit> rename(RenameParams params) {
        String uri = params.getTextDocument().getUri();
        if (lastContent.get(uri) == null)
            return CompletableFuture.completedFuture(null);

        return ensureFreshAndConfirm(uri, "Rename").thenCompose(proceed -> {
            if (!proceed) return CompletableFuture.completedFuture(null);
            try {
                System.err.println("[rename] lastContent URIs (" + lastContent.size() + "):");
                lastContent.keySet().forEach(k -> System.err.println("[rename]   " + k));
                OpenJMLSettings renameS = settingsForUri(uri);
                if (renameS == null) return null;
                WorkspaceEdit edit = Renamer.rename(
                        uri,
                        params.getPosition().getLine(),
                        params.getPosition().getCharacter(),
                        params.getNewName(),
                        lastContent,
                        CheckRunner.getASTCache(),
                        renameS);
                // Proactively update lastContent for open files modified by the rename.
                // Eclipse (and some other clients) do not send textDocument/didChange
                // after applying a server-initiated WorkspaceEdit, so the server must
                // update its own snapshot to avoid serving stale content on the next check.
                if (edit != null && edit.getChanges() != null) {
                    System.err.println("[rename] WorkspaceEdit URIs (" + edit.getChanges().size() + "):");
                    edit.getChanges().forEach((fileUri, edits) -> {
                        boolean inLastContent = lastContent.containsKey(fileUri);
                        System.err.println("[rename]   uri=" + fileUri + " edits=" + edits.size() + " inLastContent=" + inLastContent);
                        // Do NOT patch lastContent for tracked files (inLastContent=true).
                        // Tracked files will receive a textDocument/didChange from the client
                        // computed against their pre-rename content.  If we patched here, the
                        // subsequent didChange delta would be applied on top of the post-rename
                        // content, double-applying the rename and corrupting the result
                        // (e.g. "gzzmm" patched to "gzzmm", then delta [gzzx→gzzmm] applied
                        // to "gzzmm" replaces "gzzm" leaving the trailing "m" → "gzzmmm").
                        //
                        // Non-tracked files (inLastContent=false) are skipped here because they
                        // are not in lastContent; their content arrives via the didOpen/didChange
                        // that the Eclipse client sends after applying the WorkspaceEdit.
                    });
                }
                return CompletableFuture.completedFuture(edit);
            } catch (ResponseErrorException e) {
                return CompletableFuture.failedFuture(e);
            }
        });
    }

    /**
     * Extract consecutive {@code //@ } annotation lines immediately preceding
     * {@code methodLine} in {@code content}.
     */
    private static String extractJmlSpec(String content, int methodLine) {
        String[] lines = content.split("\n", -1);
        List<String> specLines = new ArrayList<>();
        for (int i = methodLine - 1; i >= 0; i--) {
            String t = lines[i].trim();
            if (t.startsWith("//@")) {
                specLines.add(0, t);
            } else if (t.isEmpty() || t.startsWith("//") || t.startsWith("*")
                    || t.startsWith("/*") || t.startsWith("@")) {
                // skip blank lines, non-JML comments, annotations between spec and method
            } else {
                break;
            }
        }
        return String.join("\n", specLines);
    }

    /**
     * Run {@code --check --dirs path1 path2 ...} on one or more OS paths
     * (for the {@code openjml.checkJML} command).
     *
     * <p>Diagnostics are stored in {@link #checkDiags} and published via
     * {@link #publishMerged} for each affected URI.
     */
    void scheduleCheckForPaths(List<String> paths, String projectId) {
        if (paths == null || paths.isEmpty()) return;
        OpenJMLSettings s = settingsForProject(projectId);
        List<String> pathsCopy = List.copyOf(paths);

        // Snapshot dirty-file content at submission time so rapid edits during the
        // debounce window do not mutate the context passed to OpenJML.
        Map<String, String> snapshot = dirtySnapshot();

        // Debounce: cancel any previously scheduled check-paths task so that rapid
        // toolbar clicks collapse into a single check.  A 300 ms delay is short enough
        // to feel immediate but long enough to absorb a double-click burst.
        ScheduledFuture<?> prev = pendingCheckPaths;
        if (prev != null) prev.cancel(false);
        pendingCheckPaths = scheduler.schedule(() -> {
            pendingCheckPaths = null;
            executor.submit(() -> {
                try {
                    CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(pathsCopy, snapshot, s);
                    for (var entry : result.diagnosticsByUri().entrySet()) {
                        storeCheckDiags(entry.getKey(), entry.getValue());
                        publishMerged(entry.getKey());
                    }
                    // Clear stale check diags for paths that produced no diagnostics.
                    for (String path : pathsCopy) {
                        String uri;
                        try { uri = java.nio.file.Path.of(path).toUri().toString(); }
                        catch (Exception e) { continue; }
                        if (!result.diagnosticsByUri().containsKey(uri)) {
                            checkDiags.remove(uri);
                            publishMerged(uri);
                        }
                    }

                    // Report completion to the client (shown in the JML Console).
                    int total = result.diagnosticsByUri().values()
                            .stream().mapToInt(List::size).sum();
                    String summary = (total == 0)
                            ? "Check complete: no issues found"
                            : "Check complete: " + total + " issue(s) in "
                              + result.diagnosticsByUri().size() + " file(s)";
                    clientLog(summary);
                } catch (Throwable e) {
                    System.err.println("[scheduleCheckForPaths] error: " + e.getMessage());
                    clientError("Check failed: " + e.getMessage());
                }
            });
        }, 300, TimeUnit.MILLISECONDS);
    }

    /**
     * Run {@code --esc --dirs path1 path2 ...} on one or more OS paths
     * (for the {@code openjml.runEsc} command).
     *
     * <p>Each path may be a {@code .java} file or a directory processed recursively.
     * Diagnostics are published per source file.  Code-lens status is updated for
     * any URIs that are currently open in the editor.
     */
    void scheduleEscForPaths(List<String> paths, String projectId) {
        if (paths == null || paths.isEmpty()) return;
        OpenJMLSettings s = settingsForProject(projectId);

        // Mark all directly-specified open files as UNKNOWN before submitting.
        // Methods transition to CHECKING individually as proofs start (via the
        // per-file callback), and to their final state as each proof completes.
        // Directory paths are handled after the run via the affected-URI scan.
        for (String path : paths) {
            try {
                java.nio.file.Path p = java.nio.file.Path.of(path);
                if (!java.nio.file.Files.isDirectory(p)) {
                    String uri = p.toUri().toString();
                    if (lastContent.containsKey(uri)) markAllMethodStatus(uri, MethodStatus.UNKNOWN);
                }
            } catch (Exception ignored) {}
        }
        refreshCodeLenses();

        // Snapshot dirty-file content before submitting so edits during the run
        // do not mutate the context map passed to OpenJML.
        Map<String, String> escSnapshot = dirtySnapshot();

        // Use the first path as a sentinel key to track this batch in the running-tasks maps.
        // cancelEsc(null) iterates all keys, so any unique key causes it to be cancelled.
        String batchKey = paths.get(0);
        Future<?> prevBatch = runningEscTasks.remove(batchKey);
        if (prevBatch != null) prevBatch.cancel(false);
        IAPI prevBatchApi = runningEscApis.remove(batchKey);
        if (prevBatchApi != null) prevBatchApi.cancelEsc();

        // Track the per-file URIs registered in runningEscApis during RUNNING events so
        // they can be cleaned up in the finally block when the batch completes.
        java.util.Set<String> batchUriKeys =
                java.util.Collections.newSetFromMap(new java.util.concurrent.ConcurrentHashMap<>());
        Future<?> batchFuture = s.escPool.submit(() -> {
            try {
                Consumer<IAPI> hook = api -> runningEscApis.put(batchKey, api);
                // Publish ESC diagnostics progressively as each method's proof starts/completes.
                // The callback fires on each RUNNING event (method proof start), receiving the
                // simple name of the method just starting.  Flip only that method to CHECKING;
                // other methods stay UNKNOWN until their own RUNNING event fires.  Then
                // updateEscStatusPartial updates completed methods to their final status.
                CheckRunner.DirCheckResult result = CheckRunner.runEscDirWithContext(
                        paths, escSnapshot, s, (uri, methodName, diags, partialResults) -> {
                    if (client == null) return;
                    if (diags == null) {
                        // RUNNING event: this method just started proving — flip it to CHECKING.
                        // diags == null is the sentinel used by runEscDir/runEscDirWithContext to
                        // distinguish a start event from a completion event.
                        // Also register the batch IAPI under this file's URI so that a Cancel
                        // code-lens click (which looks up by file URI) can find it.
                        IAPI batchApi = runningEscApis.get(batchKey);
                        if (batchApi != null) { runningEscApis.put(uri, batchApi); batchUriKeys.add(uri); }
                        markMethodCheckingByName(uri, methodName);
                        executor.execute(() -> { publishMerged(uri); refreshCodeLenses(); });
                    } else {
                        // Completion event: update diagnostics and final status progressively.
                        if (!diags.isEmpty()) storeEscDiags(uri, diags);
                        if (partialResults.containsValue(IProverResult.UNSAT)) {
                            addVerifiedDiagnostics(uri, partialResults, null);
                        }
                        updateEscStatusPartial(uri, diags, partialResults);
                        executor.execute(() -> { publishMerged(uri); refreshCodeLenses(); });
                    }
                }, hook);
                if (client == null) return;
                // After the full run, publish the final state for every affected file
                // (catches any remaining diagnostics not yet covered by the callback).
                for (var entry : result.diagnosticsByUri().entrySet()) {
                    storeEscDiags(entry.getKey(), entry.getValue());
                    publishMerged(entry.getKey());
                }
                // Clear ESC diagnostics for files that had none but are currently open.
                for (String path : paths) {
                    String uri;
                    try { uri = java.nio.file.Path.of(path).toUri().toString(); }
                    catch (Exception e) { continue; }
                    if (!result.diagnosticsByUri().containsKey(uri) && lastContent.containsKey(uri)) {
                        storeEscDiags(uri, List.of());
                        publishMerged(uri);
                    }
                }
                // Update code-lens status for ALL open files touched by this ESC run,
                // including fully-verified files that have no diagnostics (and therefore
                // are absent from result.diagnosticsByUri()).
                for (String uri : new java.util.HashSet<>(lastContent.keySet())) {
                    if (isUriAffectedByPaths(uri, paths)) {
                        List<Diagnostic> diags =
                                result.diagnosticsByUri().getOrDefault(uri, List.of());
                        updateEscStatus(uri, diags,
                                result.proofResults(), result.exitCode(), List.of());
                        publishMerged(uri);
                    }
                }
            } catch (Throwable e) {
                System.err.println("[scheduleEscForPaths] error: " + e.getMessage());
            } finally {
                runningEscApis.remove(batchKey);
                runningEscTasks.remove(batchKey);
                // Clean up per-file URI entries registered during RUNNING events.
                batchUriKeys.forEach(runningEscApis::remove);
            }
        });
        runningEscTasks.put(batchKey, batchFuture);
    }

    /**
     * Recursively walk {@code paths} (OS files or directories) collecting all
     * {@code .java} files, deduplicating by path.
     */
    private static List<java.nio.file.Path> collectJavaFiles(List<String> paths) {
        List<java.nio.file.Path> result = new java.util.ArrayList<>();
        java.util.Set<java.nio.file.Path> seen = new java.util.LinkedHashSet<>();
        for (String p : paths) {
            java.nio.file.Path root = java.nio.file.Path.of(p);
            if (!java.nio.file.Files.exists(root)) continue;
            try (var stream = java.nio.file.Files.walk(root)) {
                stream.filter(f -> java.nio.file.Files.isRegularFile(f)
                                && f.toString().endsWith(".java"))
                      .forEach(f -> { if (seen.add(f)) result.add(f); });
            } catch (java.io.IOException e) {
                System.err.println("[collectJavaFiles] error walking " + p + ": " + e);
            }
        }
        return result;
    }

    /**
     * Split-by-file ESC: recursively expand {@code paths} to individual {@code .java}
     * files and submit each as a separate whole-file ESC task on {@link OpenJMLSettings#escPool},
     * giving bounded parallelism (default 5 concurrent tasks).
     */
    void scheduleEscSplitByFile(List<String> paths, String projectId) {
        if (paths == null || paths.isEmpty()) return;
        OpenJMLSettings s = settingsForProject(projectId);
        Map<String, String> snapshot = dirtySnapshot();

        for (java.nio.file.Path javaFile : collectJavaFiles(paths)) {
            String filePath = javaFile.toString();
            String uri = javaFile.toUri().toString();
            String content = snapshot.get(uri);
            // Cancel any previous whole-file ESC task for this URI.
            Future<?> prev = runningEscTasks.remove(uri);
            if (prev != null) prev.cancel(false);
            IAPI prevApi = runningEscApis.remove(uri);
            if (prevApi != null) prevApi.cancelEsc();
            markAllMethodStatus(uri, MethodStatus.UNKNOWN);
            Future<?> f = s.escPool.submit(() -> {
                try {
                    CheckRunner.CheckResult result = (content != null)
                            ? CheckRunner.escWithContext(uri, content, snapshot, s,
                                    api -> runningEscApis.put(uri, api),
                                    methodDecl -> { markMethodCheckingByName(uri, methodDecl.name.toString()); executor.execute(() -> { publishMerged(uri); refreshCodeLenses(); }); })
                            : CheckRunner.runEscFile(filePath, uri, s,
                                    api -> runningEscApis.put(uri, api),
                                    methodDecl -> { markMethodCheckingByName(uri, methodDecl.name.toString()); executor.execute(() -> { publishMerged(uri); refreshCodeLenses(); }); });
                    storeEscDiags(uri, result.diagnostics());
                    updateEscStatus(uri, result.diagnostics(), result.proofResults(),
                            result.exitCode(), result.foreignMessages());
                    publishMerged(uri);
                    refreshCodeLenses();
                } catch (Throwable t) {
                    System.err.println("[scheduleEscSplitByFile] error for " + uri + ": " + t);
                } finally {
                    runningEscTasks.remove(uri);
                    runningEscApis.remove(uri);
                }
            });
            runningEscTasks.put(uri, f);
        }
        // Push the initial UNKNOWN state to the client now that all files are queued.
        refreshCodeLenses();
    }

    /**
     * Split-by-method ESC: recursively expand {@code paths} to individual {@code .java}
     * files, discover methods in each (AST cache preferred, regex fallback), and submit
     * each method as a separate ESC task on {@link OpenJMLSettings#escPool}.
     *
     * <p>File content is read synchronously before task submission so that method
     * discovery and all per-method lambdas share a coherent snapshot.
     */
    void scheduleEscSplitByMethod(List<String> paths, String projectId) {
        if (paths == null || paths.isEmpty()) return;
        OpenJMLSettings s = settingsForProject(projectId);
        Map<String, String> snapshot = dirtySnapshot();

        for (java.nio.file.Path javaFile : collectJavaFiles(paths)) {
            String uri = javaFile.toUri().toString();

            // Resolve content: prefer in-memory, fall back to reading disk now so that
            // method discovery and task lambdas all see the same file version.
            String content = snapshot.get(uri);
            if (content == null) {
                try { content = java.nio.file.Files.readString(javaFile); }
                catch (Exception e) {
                    System.err.println("[scheduleEscSplitByMethod] cannot read " + javaFile + ": " + e);
                    continue;
                }
            }
            final String finalContent = content;

            // Discover methods: AST cache preferred, regex fallback (same as codeLens).
            ASTCache.Entry astEntry = CheckRunner.getASTCache().get(uri);
            List<JavaSourceScanner.MethodInfo> methods = (astEntry != null)
                    ? JavaSourceScanner.findMethodsFromAst(astEntry.ast(), content)
                    : JavaSourceScanner.findMethods(content);
            if (methods.isEmpty()) continue;

            // Mark all methods in this file as CHECKING before submitting.
            Map<Integer, MethodStatus> checking = new java.util.HashMap<>();
            for (JavaSourceScanner.MethodInfo m : methods)
                checking.put(m.startLine(), MethodStatus.CHECKING);
            methodEscStatus.put(uri, checking);
            refreshCodeLenses();

            for (JavaSourceScanner.MethodInfo method : methods) {
                final String methodName = method.name();
                submitEscForMethod(uri, method,
                        hook -> CheckRunner.escMethodWithContext(
                                uri, finalContent, methodName, snapshot, s, hook),
                        s.escPool);
            }
        }
    }

    /**
     * Returns true if {@code uri} (a {@code file:///} URI of an open file) is
     * covered by at least one entry in {@code paths} (OS file or directory paths).
     */
    private static boolean isUriAffectedByPaths(String uri, List<String> paths) {
        for (String path : paths) {
            try {
                java.nio.file.Path p = java.nio.file.Path.of(path);
                String pathUri = p.toUri().toString(); // ends with '/' for directories
                if (uri.equals(pathUri) || uri.startsWith(pathUri)) return true;
            } catch (Exception ignored) {}
        }
        return false;
    }

    /**
     * Run {@code --rac --dirs path1 path2 ...} on one or more OS paths
     * (for the {@code openjml.runRac} command).
     *
     * <p>RAC subsumes {@code --check}, so existing check diagnostics are cleared
     * for all affected URIs before publishing the RAC result.  Diagnostics are
     * stored in {@link #racDiags} and published via {@link #publishMerged} for
     * each affected URI.
     */
    void scheduleRacForPaths(List<String> paths, String projectId, String outputDir) {
        if (paths == null || paths.isEmpty()) return;
        OpenJMLSettings base = settingsForProject(projectId);
        // In the new Eclipse format, outputDir is null (already in base.racOutputDir via ProjectConfig).
        // In the old VS Code format, outputDir is passed explicitly and must override.
        OpenJMLSettings s;
        if (outputDir != null && !outputDir.isEmpty()) {
            s = new OpenJMLSettings(base);
            s.racOutputDir = outputDir;
        } else {
            s = base;
        }
        List<String> pathsCopy = List.copyOf(paths);
        executor.submit(() -> {
            try {
                CheckRunner.CheckResult result = CheckRunner.runRacPaths(pathsCopy, s);
                result.allDiagnostics().forEach((uri, diags) -> {
                    checkDiags.remove(uri);  // RAC subsumes check; clear stale check markers
                    racDiags.put(uri, diags);
                    publishMerged(uri);
                });
                // Clear stale check/rac diags for paths not in the result.
                for (String path : pathsCopy) {
                    String uri;
                    try { uri = java.nio.file.Path.of(path).toUri().toString(); }
                    catch (Exception e) { continue; }
                    if (!result.allDiagnostics().containsKey(uri)) {
                        checkDiags.remove(uri);
                        racDiags.remove(uri);
                        publishMerged(uri);
                    }
                }
                int total = result.allDiagnostics().values()
                        .stream().mapToInt(List::size).sum();
                if (result.exitCode() == 0) {
                    clientLog("RAC compile succeeded for " + pathsCopy.size() + " path(s)");
                } else {
                    clientLog("RAC compile failed: " + total + " issue(s) in "
                            + result.allDiagnostics().size() + " file(s)");
                    result.allDiagnostics().forEach((uri, diags) -> {
                        if (!diags.isEmpty()) {
                            String fname = uri.contains("/") ? uri.substring(uri.lastIndexOf('/') + 1) : uri;
                            clientLog("  " + fname + ": " + diags.size() + " issue(s)");
                        }
                    });
                }
            } catch (Throwable e) {
                System.err.println("[scheduleRacForPaths] error: " + e.getMessage());
                clientError("RAC failed: " + e.getMessage());
            }
        });
    }

    /**
     * Run ESC on the given URI immediately (for the {@code openjml.runEsc} command).
     * Uses the file on disk; if the file does not exist the call is a no-op.
     */
    /**
     * Return the flat semantic token integer data for {@code uri}, or an empty
     * list if the file is not currently open.  Called by the workspace service
     * in response to the {@code openjml.getSemanticTokens} command so the VS
     * Code extension can register a direct {@code DocumentSemanticTokensProvider}
     * that merges additively with the Red Hat Java extension's tokens.
     */
    List<Integer> getSemanticTokens(String uri) {
        String content = lastContent.get(uri);
        if (content == null) return List.of();
        // "regex" strategy: always use regex (instant, works before first --check).
        // "ast" strategy (default): prefer AST-based when an attributed AST is
        // available (no false positives), fall back to regex before first --check.
        // .jml files never have a standalone AST — always use regex for them.
        if (!globalSettings.isRegexColoring() && !uri.endsWith(".jml")) {
            ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
            if (entry != null) {
                try {
                    // Guard: if the cached AST was built from a different version of the
                    // file, its character offsets may exceed the current content length,
                    // causing StringIndexOutOfBoundsException.  Fall through to regex.
                    CharSequence astSrc = entry.ast().sourcefile.getCharContent(false);
                    if (astSrc.length() == content.length()) {
                        return SemanticTokensProvider.computeTokensFromAst(entry, content).getData();
                    }
                } catch (Exception ignored) {}
            }
        }
        return SemanticTokensProvider.computeTokens(content).getData();
    }

    /**
     * Handle {@code textDocument/semanticTokens/full} requests from LSP clients
     * (e.g. Eclipse via LSP4E's {@code SemanticHighlightReconcilerStrategy}).
     */
    @Override
    public CompletableFuture<org.eclipse.lsp4j.SemanticTokens> semanticTokensFull(
            org.eclipse.lsp4j.SemanticTokensParams params) {
        return CompletableFuture.supplyAsync(() -> {
            String uri = params.getTextDocument().getUri();
            List<Integer> data = getSemanticTokens(uri);
            return new org.eclipse.lsp4j.SemanticTokens(data);
        });
    }

    /**
     * Return all indexed declarations whose simple name contains {@code query}
     * (case-insensitive).  An empty query returns all declarations.
     *
     * <p>Only declarations in currently-open files (present in {@code lastContent})
     * are returned, since their source is needed for offset→line:col conversion.
     *
     * <p>Called by {@link OpenJMLWorkspaceService} in response to
     * {@code workspace/symbol} requests (Cmd+T / Ctrl+T in VS Code).
     */
    /** Query the declaration index across all projects. */
    List<SymbolInformation> symbols(String query) {
        return symbols(query, null);
    }

    /**
     * Query the declaration index, optionally restricted to one project.
     *
     * <p>The {@code query} string may encode a project root using a newline
     * separator: {@code "<projectRoot>\n<identifier>"}.  When a newline is
     * present the part before it is treated as the project root filter and the
     * part after it is the identifier to match.  Plain queries (no newline) are
     * matched against all projects, preserving backward compatibility with
     * VS Code and other single-project clients.
     *
     * @param query       identifier to match (exact case-sensitive), optionally
     *                    prefixed with a project root and newline; empty = return all
     * @param projectRoot explicit project-root filter; takes precedence over any
     *                    root encoded in {@code query}; {@code null} = no filter
     */
    List<SymbolInformation> symbols(String query, String projectRoot) {
        if (navCacheDirty) {
            clientLog("workspace/symbol: project index not yet complete — results may be incomplete");
        }
        String raw = query == null ? "" : query.trim();

        // Extract an encoded project root from the query string.
        // Format: "<projectRoot>\n<identifier>" — newlines cannot appear in
        // Java identifiers, so this separator is unambiguous.
        // An explicit projectRoot argument takes precedence.
        int nlIdx = raw.indexOf('\n');
        if (nlIdx >= 0 && projectRoot == null) {
            projectRoot = raw.substring(0, nlIdx).trim();
            raw = raw.substring(nlIdx + 1).trim();
        }

        // Strip any surrounding quote characters that a client might accidentally include.
        if (raw.length() >= 2
                && ((raw.startsWith("\"") && raw.endsWith("\""))
                    || (raw.startsWith("'") && raw.endsWith("'")))) {
            raw = raw.substring(1, raw.length() - 1).trim();
        }
        final String effectiveQuery = raw;
        System.err.println("[symbols] query=\"" + effectiveQuery + "\""
                + (projectRoot != null ? " root=\"" + projectRoot + "\"" : "")
                + "  navCacheDirty=" + navCacheDirty);
        List<SymbolInformation> result = new ArrayList<>();
        CheckRunner.getASTCache().forEachDeclaration(projectRoot, (sym, loc) -> {
            String name = sym.name.toString();
            // Skip synthetic names (<init>, <clinit>, empty).
            if (name.isEmpty() || name.startsWith("<")) return;
            // Filter by query: exact case-sensitive match; empty query = accept all.
            if (!effectiveQuery.isEmpty() && !name.equals(effectiveQuery)) return;
            // Offset → Position requires source content.
            // Prefer in-memory content (for unsaved edits); fall back to disk.
            String content = lastContent.get(loc.uri());
            if (content == null) {
                String path = CheckRunner.uriToPath(loc.uri());
                if (path != null) {
                    try { content = java.nio.file.Files.readString(java.nio.file.Path.of(path)); }
                    catch (java.io.IOException e) {
                        System.err.println("[OpenJML] workspace/symbol: cannot read " + loc.uri()
                                + ": " + e.getMessage());
                    }
                }
            }
            if (content == null) return;
            Position pos = offsetToPosition(content, loc.charOffset());
            var location = new Location(loc.uri(), new Range(pos, pos));
            result.add(new SymbolInformation(name, symbolKind(sym), location));
        });
        System.err.println("[symbols] returning " + result.size() + " result(s)"
                + (result.isEmpty() ? "" : ", first URI=" + result.get(0).getLocation().getUri()));
        return result;
    }

    /** Convert a character offset to a 0-based LSP {@link Position}. */
    private static Position offsetToPosition(String content, int offset) {
        int line = 0, col = 0;
        int end = Math.min(offset, content.length());
        for (int i = 0; i < end; i++) {
            if (content.charAt(i) == '\n') { line++; col = 0; }
            else col++;
        }
        return new Position(line, col);
    }

    /** Map a javac {@link com.sun.tools.javac.code.Symbol} to an LSP {@link SymbolKind}. */
    private static SymbolKind symbolKind(com.sun.tools.javac.code.Symbol sym) {
        if (sym instanceof com.sun.tools.javac.code.Symbol.ClassSymbol cs) {
            if (cs.isEnum())      return SymbolKind.Enum;
            if (cs.isInterface()) return SymbolKind.Interface;
            return SymbolKind.Class;
        }
        if (sym instanceof com.sun.tools.javac.code.Symbol.MethodSymbol ms) {
            return ms.isConstructor() ? SymbolKind.Constructor : SymbolKind.Method;
        }
        if (sym instanceof com.sun.tools.javac.code.Symbol.VarSymbol vs) {
            return (vs.owner instanceof com.sun.tools.javac.code.Symbol.MethodSymbol)
                    ? SymbolKind.Variable : SymbolKind.Field;
        }
        return SymbolKind.Object;
    }

    // -----------------------------------------------------------------------
    // Per-project path overrides
    // -----------------------------------------------------------------------

    /**
     * Returns a per-invocation copy of {@link #globalSettings} with path/settings fields
     * overridden by any non-empty arguments, or {@code globalSettings} itself when all
     * arguments are null/empty.  The {@link OpenJMLSettings#escPool} is always shared.
     *
     * @param sourcePath      override for {@code -sourcepath} (null/empty = keep)
     * @param classPath       override for {@code -classpath}  (null/empty = keep)
     * @param specsPath       override for {@code --specs-path} (null/empty = keep)
     * @param propertiesFile  override for {@code generatedPropertiesFile} (null/empty = keep)
     * @param outputDir       override for {@code racOutputDir} (null/empty = keep)
     */
    private OpenJMLSettings withContext(String sourcePath, String classPath,
                                         String specsPath, String propertiesFile,
                                         String outputDir) {
        boolean hasSrc = sourcePath     != null && !sourcePath.isEmpty();
        boolean hasCp  = classPath      != null && !classPath.isEmpty();
        boolean hasSp  = specsPath      != null && !specsPath.isEmpty();
        boolean hasPf  = propertiesFile != null && !propertiesFile.isEmpty();
        boolean hasOd  = outputDir      != null && !outputDir.isEmpty();
        if (!hasSrc && !hasCp && !hasSp && !hasPf && !hasOd) return globalSettings;
        OpenJMLSettings s = new OpenJMLSettings(globalSettings);
        if (hasSrc) s.sourcePath              = sourcePath;
        if (hasCp)  s.classPath               = classPath;
        if (hasSp)  s.specsPath               = specsPath;
        if (hasPf)  s.generatedPropertiesFile  = propertiesFile;
        if (hasOd)  s.racOutputDir             = outputDir;
        return s;
    }

    // -----------------------------------------------------------------------
    // Per-project settings registry
    // -----------------------------------------------------------------------

    /**
     * Project ID → per-project settings.  Always populated after {@code initialize}
     * completes: VS Code / bare-LSP clients get a single {@code "__workspace__"} entry
     * (which acts as a wildcard when it has no root paths); Eclipse multi-project clients
     * get one entry per JML-natured project.  Never empty once the server is initialized.
     */
    private final java.util.concurrent.ConcurrentHashMap<String, OpenJMLSettings>
            projectSettings = new java.util.concurrent.ConcurrentHashMap<>();

    /**
     * Rebuild the per-project settings registry from a {@code projects} list.
     *
     * <p>Called both from {@code workspace/didChangeConfiguration} (Eclipse client sends
     * explicit project configs) and from {@link OpenJMLLanguageServer#initialize} after
     * synthesizing the {@code "__workspace__"} project for single-project clients.
     *
     * <p>For each project, per-project fields (sourcePath, classPath, specsPath,
     * propertiesFile, generatedPropertiesFile, outputDir) override the global settings
     * when non-null; all other fields are inherited.  The {@code "__workspace__"} project
     * has no overrides and therefore inherits everything from global settings.
     */
    void updateProjectSettings(List<OpenJMLSettings.ProjectConfig> configs) {
        projectSettings.clear();
        if (configs == null) return;
        for (OpenJMLSettings.ProjectConfig cfg : configs) {
            if (cfg.id == null || cfg.id.isBlank()) continue;
            OpenJMLSettings s = new OpenJMLSettings(globalSettings);
            s.sourcePath              = cfg.sourcePath              != null ? cfg.sourcePath              : "";
            s.classPath               = cfg.classPath               != null ? cfg.classPath               : "";
            s.specsPath               = cfg.specsPath               != null ? cfg.specsPath               : globalSettings.specsPath;
            s.propertiesFile          = cfg.propertiesFile          != null ? cfg.propertiesFile          : globalSettings.propertiesFile;
            s.generatedPropertiesFile = cfg.generatedPropertiesFile != null ? cfg.generatedPropertiesFile : globalSettings.generatedPropertiesFile;
            s.racOutputDir            = cfg.outputDir               != null ? cfg.outputDir               : globalSettings.racOutputDir;
            // Store rootPaths so settingsForUri can match file URIs to this project.
            if (cfg.rootPaths != null && !cfg.rootPaths.isEmpty())
                s.rootPaths = String.join(java.io.File.pathSeparator, cfg.rootPaths);
            projectSettings.put(cfg.id, s);
        }
        System.err.println("[OpenJML] project registry updated: " + projectSettings.keySet());
    }

    /** Returns {@code true} if {@code projectId} is in the current project registry. */
    boolean isKnownProject(String projectId) {
        return projectSettings.containsKey(projectId);
    }

    /**
     * Returns the settings for the given project ID, or global settings if the ID is
     * null/blank.  Logs an error if the ID is non-blank but not found in the registry
     * (indicates the client submitted an unrecognized project name).
     */
    OpenJMLSettings settingsForProject(String projectId) {
        if (projectId == null || projectId.isBlank()) return globalSettings;
        OpenJMLSettings s = projectSettings.get(projectId);
        if (s == null) {
            clientError("OpenJML: unknown project ID '" + projectId
                    + "' — not in the registered project list " + projectSettings.keySet()
                    + ". Using global settings as fallback.");
            return globalSettings;
        }
        return s;
    }

    /**
     * Returns the settings for the project that owns {@code uri}, matched by
     * {@link OpenJMLSettings#rootPaths}.
     *
     * <p>Projects are checked in two passes:
     * <ol>
     *   <li>Projects with non-empty {@code rootPaths}: the URI's file path must start
     *       with one of the roots (specific match).</li>
     *   <li>Projects with null or empty {@code rootPaths}: treated as a wildcard
     *       catch-all.  The synthesized {@code "__workspace__"} project falls into this
     *       category when the client provided no workspace folders.</li>
     * </ol>
     *
     * <p>Returns {@code null} if no project — specific or wildcard — matches the URI.
     * This indicates the file is outside all configured projects (e.g. a file in a
     * non-JML-natured Eclipse project); callers should skip processing.
     */
    OpenJMLSettings settingsForUri(String uri) {
        String filePath;
        try { filePath = java.net.URI.create(uri).getPath(); }
        catch (Exception e) { return null; }
        String sep = java.io.File.separator;
        OpenJMLSettings wildcard = null;
        for (OpenJMLSettings s : projectSettings.values()) {
            if (s.rootPaths == null || s.rootPaths.isBlank()) {
                wildcard = s;   // catch-all: matches anything not claimed by a specific project
                continue;
            }
            for (String root : s.rootPaths.split(java.io.File.pathSeparator)) {
                if (root.isBlank()) continue;
                String r = root.endsWith(sep) ? root : root + sep;
                if (filePath.startsWith(r)) return s;
            }
        }
        return wildcard;   // null if no wildcard project is registered
    }

    // -----------------------------------------------------------------------
    // Explicit-check commands (from Eclipse CheckJML handler)
    // -----------------------------------------------------------------------

    /**
     * Type-check the given URI on demand (for the {@code openjml.checkJML} command).
     *
     * <p>If the file is currently open, checks the in-memory content so that
     * unsaved edits are included.  Otherwise falls back to the on-disk version.
     * Per-project {@code sourcePath} and {@code classPath} overrides are applied
     * when non-empty; {@code null} or empty means use the global settings.
     */
    void scheduleCheckForUri(String uri, String projectId) {
        OpenJMLSettings s = projectId != null ? settingsForProject(projectId) : settingsForUri(uri);
        final String content = lastContent.get(uri);
        executor.submit(() -> runCheckContent(uri, content, s));
    }

    /**
     * Trigger a --check recheck of an already-open file (e.g. when focus returns
     * to it after its dependencies were edited).  Uses in-memory content so that
     * unsaved edits are included.  No-op if the file is not currently open.
     */
    void recheckUri(String uri) {
        if (settingsForUri(uri) == null) return;
        String content = lastContent.get(uri);
        if (content == null) return;
        // Skip if nothing has changed since the last completed check.
        if (content.equals(lastCheckedContent.get(uri))) return;
        // Skip if a check is already queued or running for this URI (e.g. didOpen
        // schedules a check, then onDidChangeActiveTextEditor fires 200ms later).
        CompletableFuture<Void> pending = lastCheckFuture.get(uri);
        if (pending != null && !pending.isDone()) return;
        executor.submit(() -> runCheckContent(uri, content));
    }

    void scheduleEscForUri(String uri, String projectId) {
        OpenJMLSettings s = projectId != null ? settingsForProject(projectId) : settingsForUri(uri);
        if (s.isEscApiMode()) {
            submitEscApiWorkList(uri, s);
        } else if (s.isFreshParallelMode()) {
            submitFreshParallelWorkList(uri, s);
        } else {
            scheduleEscFile(uri, s);
        }
    }

    /**
     * Submit the api-engine ESC work list for {@code uri}.
     *
     * <p>Each method in the file is submitted as a separate task to
     * {@link OpenJMLSettings#escPool}.  As each method completes its code-lens
     * status is updated immediately so the user sees progress.  After all
     * methods finish a final {@link #publishMerged} flushes the accumulated
     * diagnostics.
     */
    private void submitEscApiWorkList(String uri) {
        submitEscApiWorkList(uri, globalSettings);
    }

    private void submitEscApiWorkList(String uri, OpenJMLSettings s) {
        Future<?> prev = runningEscTasks.remove(uri);
        if (prev != null) prev.cancel(false);

        long myGen = escGen.computeIfAbsent(uri, k -> new AtomicLong()).incrementAndGet();
        markEscChecking(uri);

        CompletableFuture<CheckRunner.CheckResult> cf =
                CheckRunner.runDoEscFileAsync(uri, s, methodResult -> {
                    // Called on a pool thread as each method finishes — update its
                    // code-lens status immediately so the user sees progress.
                    if (escGen.get(uri).get() != myGen) return;
                    updateSingleMethodEscStatus(uri, methodResult);
                    refreshCodeLenses();
                });

        cf.thenAccept(result -> {
            if (escGen.get(uri).get() != myGen) return;
            storeEscDiags(uri, result.diagnostics());
            if (result.isInternalError()) {
                System.err.println("[OpenJML] ESC internal error (exit code " + result.exitCode() + ")");
                markAllMethodStatus(uri, MethodStatus.CHECK_ERROR);
                refreshCodeLenses();
            } else {
                updateEscStatus(uri, result.diagnostics(), result.proofResults(),
                        result.exitCode(), result.foreignMessages());
            }
            publishMerged(uri);
        }).exceptionally(t -> {
            System.err.println("[OpenJML] ESC (api) failed: " + t);
            if (escGen.get(uri).get() == myGen) {
                updateEscStatus(uri, List.of(), Map.of(), -1, List.of());
                refreshCodeLenses();
            }
            return null;
        }).whenComplete((v, t) -> runningEscTasks.remove(uri));

        runningEscTasks.put(uri, cf);
    }

    /**
     * Submit the fresh-parallel ESC work list for {@code uri}.
     *
     * <p>Each method gets a fresh IAPI instance running on {@link OpenJMLSettings#escPool};
     * all run truly concurrently.  Per-method and final callbacks are the same as
     * {@link #submitEscApiWorkList}.
     */
    private void submitFreshParallelWorkList(String uri) {
        submitFreshParallelWorkList(uri, globalSettings);
    }

    private void submitFreshParallelWorkList(String uri, OpenJMLSettings s) {
        Future<?> prev = runningEscTasks.remove(uri);
        if (prev != null) prev.cancel(true);

        long myGen = escGen.computeIfAbsent(uri, k -> new AtomicLong()).incrementAndGet();
        markEscChecking(uri);

        String content = lastContent.get(uri);
        CompletableFuture<CheckRunner.CheckResult> cf =
                CheckRunner.runFreshParallelEscFileAsync(uri, content, s, methodResult -> {
                    if (escGen.get(uri).get() != myGen) return;
                    updateSingleMethodEscStatus(uri, methodResult);
                    refreshCodeLenses();
                });

        cf.thenAccept(result -> {
            if (escGen.get(uri).get() != myGen) return;
            escDiags.put(uri, result.diagnostics());
            if (result.isInternalError()) {
                System.err.println("[OpenJML] ESC (fresh) internal error (exit code " + result.exitCode() + ")");
                markAllMethodStatus(uri, MethodStatus.CHECK_ERROR);
                refreshCodeLenses();
            } else {
                updateEscStatus(uri, result.diagnostics(), result.proofResults(),
                        result.exitCode(), result.foreignMessages());
            }
            publishMerged(uri);
        }).exceptionally(t -> {
            System.err.println("[OpenJML] ESC (fresh) failed: " + t);
            if (escGen.get(uri).get() == myGen) {
                updateEscStatus(uri, List.of(), Map.of(), -1, List.of());
                refreshCodeLenses();
            }
            return null;
        }).whenComplete((v, t) -> runningEscTasks.remove(uri));

        runningEscTasks.put(uri, cf);
    }

    /**
     * Update the code-lens status for a single method that completed doESC.
     * Diagnostics for that method are applied; other methods' statuses are
     * unchanged and will be overwritten by the final {@link #updateEscStatus} call.
     */
    private void updateSingleMethodEscStatus(String uri,
                                              CheckRunner.MethodEscResult r) {
        String content = lastContent.get(uri);
        if (content == null) return;
        List<JavaSourceScanner.MethodInfo> methods = JavaSourceScanner.findMethods(content);
        for (JavaSourceScanner.MethodInfo m : methods) {
            if (!m.name().equals(r.name())) continue;
            Map<Integer, MethodStatus> statuses =
                    new HashMap<>(methodEscStatus.getOrDefault(uri, Map.of()));
            statuses.put(m.startLine(),
                    proofResultToStatus(r.kind(), r.diags(),
                            m.startLine(), m.endLine(), r.exitCode(), false));
            methodEscStatus.put(uri, statuses);
            break;
        }
    }

    /**
     * Run ESC on a single method in the given URI (for the {@code openjml.runEscForMethod}
     * command).  {@code methodName} is the fully-qualified name passed to {@code --method}.
     *
     * <p>Unlike a full-file ESC, only the target method's code-lens status and its
     * diagnostics (within its line range) are updated; other methods are left unchanged.
     */
    void scheduleEscForMethod(String uri, String methodName, String projectId) {
        OpenJMLSettings s = projectId != null ? settingsForProject(projectId) : settingsForUri(uri);
        String content = lastContent.get(uri);
        JavaSourceScanner.MethodInfo target = findMethod(uri, content, methodName);

        // If the method is currently CHECKING, the user clicked "✕ Cancel":
        // abort the in-flight proof only; do not stop the whole ESC run.
        if (target != null) {
            MethodStatus current = methodEscStatus
                    .getOrDefault(uri, Map.of())
                    .getOrDefault(target.startLine(), MethodStatus.UNKNOWN);
            if (current.result() == EscResult.CHECKING) {
                String methodKey = uri + "#" + target.name() + "@" + target.startLine();
                System.out.println("[OpenJML] Cancel lens pressed for " + target.name()
                        + " in " + uri
                        + "; methodApis=" + runningEscMethodApis.containsKey(methodKey)
                        + " fileApis=" + runningEscApis.containsKey(uri)
                        + " allApiKeys=" + runningEscApis.keySet());
                abortCurrentProof(methodKey);
                return;
            }
        }

        // rawName() carries "owner.FQN.methodName(sig)" for AST-derived MethodInfo entries,
        // which OpenJML's --method flag accepts.  For regex-derived entries (before the first
        // check) rawName() is the bare method name, which still works for simple cases.
        final String escMethodName = (target != null) ? target.rawName() : methodName;

        if (s.isEscApiMode()) {
            // Submit through escPool so this request joins the same shared queue
            // as any in-flight runDoEscFileAsync tasks for the same URI.
            // doESC path uses the cached IAPI directly; hook not applicable here.
            submitEscForMethod(uri, target,
                    hook -> CheckRunner.runDoEscMethod(uri, escMethodName, s),
                    s.escPool);
        } else {
            String contentForMethod = lastContent.get(uri);
            Map<String, String> snapshot = dirtySnapshot();
            if (contentForMethod != null) {
                final String c = contentForMethod;
                submitEscForMethod(uri, target,
                        hook -> CheckRunner.escMethodWithContext(uri, c, escMethodName, snapshot, s, hook),
                        s.escPool);
            } else {
                String filePath = CheckRunner.uriToPath(uri);
                if (filePath != null)
                    submitEscForMethod(uri, target,
                            hook -> CheckRunner.runEscFileMethod(filePath, uri, escMethodName, s, hook),
                            s.escPool);
            }
        }
    }

    /**
     * Locate a method in {@code content} from a name reference that is either:
     * <ul>
     *   <li>{@code "name@startLine"} — code-lens format; matched by start line
     *       so overloads are distinguished correctly, or</li>
     *   <li>a plain name or FQN — matched by simple name (first match wins;
     *       ambiguous for overloads, retained for VS Code / legacy callers).</li>
     * </ul>
     *
     * <p>Uses AST-based method discovery when a cached AST is available for
     * {@code uri}, so that {@link JavaSourceScanner.MethodInfo#rawName()} carries
     * the FQN+signature key needed to look up proof results.  Falls back to
     * the regex scanner when no AST is available (e.g. before the first check).
     */
    private static JavaSourceScanner.MethodInfo findMethod(String uri, String content,
                                                            String nameOrRef) {
        if (content == null || nameOrRef == null || nameOrRef.isEmpty()) return null;
        ASTCache.Entry astEntry = uri != null ? CheckRunner.getASTCache().get(uri) : null;
        List<JavaSourceScanner.MethodInfo> methods = (astEntry != null)
                ? JavaSourceScanner.findMethodsFromAst(astEntry.ast(), content)
                : JavaSourceScanner.findMethods(content);
        int at = nameOrRef.lastIndexOf('@');
        if (at >= 0) {
            try {
                int line = Integer.parseInt(nameOrRef.substring(at + 1));
                if (at == 0) {
                    // "@cursorLine" format (no name prefix): find the method whose range
                    // contains the cursor line, so the menu command works when the cursor
                    // is anywhere inside the method body, not just on the declaration line.
                    for (JavaSourceScanner.MethodInfo m : methods) {
                        if (m.contains(line)) return m;
                    }
                    return null;
                }
                // "name@startLine" format: exact start-line match (code-lens path).
                for (JavaSourceScanner.MethodInfo m : methods) {
                    if (m.startLine() == line) return m;
                }
            } catch (NumberFormatException ignored) {}
        }
        // Fallback: plain name or FQN — strip to simple name and match first occurrence.
        int dot = nameOrRef.lastIndexOf('.');
        String simpleName = dot >= 0 ? nameOrRef.substring(dot + 1) : nameOrRef;
        for (JavaSourceScanner.MethodInfo m : methods) {
            if (simpleName.equals(m.name())) return m;
        }
        return null;
    }

    /**
     * Submit an ESC task that targets a single method.
     *
     * <ul>
     *   <li>Cancels any running ESC task for the same URI.</li>
     *   <li>Marks only the target method as CHECKING (others are left as-is).</li>
     *   <li>On completion, replaces only the diagnostics within the target method's
     *       line range and updates only that method's code-lens status.</li>
     *   <li>Falls back to full-file behaviour if {@code target} is {@code null}.</li>
     *   <li>Exceptions from the task are logged to stderr so they are not silently lost.</li>
     * </ul>
     */
    private void submitEscForMethod(String uri, JavaSourceScanner.MethodInfo target,
            java.util.function.Function<java.util.function.Consumer<IAPI>,
                                        CheckRunner.CheckResult> task,
            ExecutorService pool) {

        // Determine the tracking key and cancel any in-flight predecessor.
        // Per-method runs use a "uri#methodName@startLine" key so concurrent runs on
        // different methods (or overloads with the same name) coexist.
        final String methodKey;
        if (target != null) {
            methodKey = uri + "#" + target.name() + "@" + target.startLine();
            Future<?> prev = runningEscMethodTasks.remove(methodKey);
            if (prev != null) prev.cancel(false);
            IAPI prevApi = runningEscMethodApis.remove(methodKey);
            if (prevApi != null) prevApi.cancelEsc();
        } else {
            // Whole-file run: cancel any previous whole-file run for this URI.
            methodKey = null;
            Future<?> prev = runningEscTasks.remove(uri);
            if (prev != null) prev.cancel(false);
            IAPI prevApi = runningEscApis.remove(uri);
            if (prevApi != null) prevApi.cancelEsc();
        }

        // Generation counter is used for whole-file runs only; per-method runs
        // on the same file coexist and do not supersede each other.
        final long myGen = (methodKey == null)
                ? escGen.computeIfAbsent(uri, k -> new AtomicLong()).incrementAndGet()
                : -1L;

        // Mark only the target method as CHECKING.
        if (target != null) {
            Map<Integer, MethodStatus> statuses =
                    new java.util.HashMap<>(methodEscStatus.getOrDefault(uri, Map.of()));
            statuses.put(target.startLine(), MethodStatus.CHECKING);
            methodEscStatus.put(uri, statuses);
            // Remove any Verified (Hint) marker for this method immediately so it
            // disappears while the re-run is in progress rather than lingering.
            List<Diagnostic> diags = new ArrayList<>(escDiags.getOrDefault(uri, List.of()));
            if (diags.removeIf(d -> DiagnosticSeverity.Hint.equals(d.getSeverity())
                    && DiagnosticConverter.SOURCE_ESC.equals(d.getSource())
                    && target.contains(d.getRange().getStart().getLine()))) {
                escDiags.put(uri, diags);
                publishMerged(uri);
            }
            refreshCodeLenses();
        } else {
            markEscChecking(uri);
        }

        Future<?> f = pool.submit(() -> {
            try {
                java.util.function.Consumer<IAPI> hook = api -> {
                    if (methodKey != null) runningEscMethodApis.put(methodKey, api);
                    else                   runningEscApis.put(uri, api);
                };
                CheckRunner.CheckResult result = task.apply(hook);
                if (result.isCommandLineError())
                    System.err.println("[OpenJML] BUG: exit code 2 (bad command-line args) from ESC-method for " + uri);
                // Generation guard: only whole-file runs can be superseded.
                if (myGen >= 0 && escGen.get(uri).get() != myGen) return;

                if (result.isInternalError()) {
                    System.err.println("[OpenJML] ESC for method: internal error (exit code " + result.exitCode() + ")");
                    storeEscDiags(uri, result.diagnostics());
                    publishMerged(uri);
                    if (target != null) {
                        Map<Integer, MethodStatus> statuses =
                                new java.util.HashMap<>(methodEscStatus.getOrDefault(uri, Map.of()));
                        statuses.put(target.startLine(), MethodStatus.CHECK_ERROR);
                        methodEscStatus.put(uri, statuses);
                        refreshCodeLenses();
                    }
                    return;
                }

                List<Diagnostic> diags = result.diagnostics();
                if (target != null) {
                    // Replace only the diagnostics inside the target method's line range.
                    int start = target.startLine();
                    int end   = target.endLine();
                    List<Diagnostic> kept = new ArrayList<>(
                            escDiags.getOrDefault(uri, List.of()));
                    kept.removeIf(d -> target.contains(d.getRange().getStart().getLine()));
                    kept.addAll(diags);
                    checkDiags.remove(uri);  // ESC subsumes check
                    escDiags.put(uri, kept);

                    // Update only the target method's code-lens status using
                    // the proof result if available, else fall back to diag count.
                    // target.rawName() is FQN+sig when AST was available for findMethod;
                    // proofResultForMethod handles both the exact-key and bare-name cases.
                    IProverResult.Kind kind = result.proofResultForMethod(
                            CheckRunner.bareMethodName(target.rawName()));
                    MethodStatus ms = proofResultToStatus(kind, diags, start, end,
                                                          result.exitCode(), result.hasForeignErrors());
                    Map<Integer, MethodStatus> statuses =
                            new java.util.HashMap<>(methodEscStatus.getOrDefault(uri, Map.of()));
                    statuses.put(start, ms);
                    methodEscStatus.put(uri, statuses);
                    addVerifiedDiagnostics(uri, result.proofResults(), target);
                } else {
                    storeEscDiags(uri, diags);
                    updateEscStatus(uri, diags, result.proofResults(), result.exitCode(),
                                        result.foreignMessages());
                }
                publishMerged(uri);
                refreshCodeLenses();
            } catch (Throwable t) {
                System.err.println("[OpenJML] ESC for method failed unexpectedly: " + t);
                if (target != null) {
                    Map<Integer, MethodStatus> statuses =
                            new java.util.HashMap<>(methodEscStatus.getOrDefault(uri, Map.of()));
                    statuses.put(target.startLine(), MethodStatus.UNKNOWN);
                    methodEscStatus.put(uri, statuses);
                    refreshCodeLenses();
                }
            } finally {
                if (methodKey != null) {
                    runningEscMethodApis.remove(methodKey);
                    runningEscMethodTasks.remove(methodKey);
                } else {
                    runningEscApis.remove(uri);
                    runningEscTasks.remove(uri);
                }
            }
        });

        if (methodKey != null) runningEscMethodTasks.put(methodKey, f);
        else                   runningEscTasks.put(uri, f);
    }

    // --- disk file-change handlers (called from OpenJMLWorkspaceService) ---

    /**
     * Called when a {@code .jml} file changes on disk outside the editor.
     * If the file is already open in the editor the editor path handles it and
     * this method returns immediately to avoid a double-check.
     */
    void handleWatchedJmlChange(String uri, FileChangeType type) {
        if (lastContent.containsKey(uri)) return;  // editor path already handles it

        if (type == FileChangeType.Deleted) {
            String javaUri = resolveCompanionJavaUri(uri, "");
            if (javaUri != null && client != null)
                client.publishDiagnostics(new PublishDiagnosticsParams(javaUri, List.of()));
            CheckRunner.getASTCache().remove(uri);
            return;
        }
        // Created or Changed: read content from disk, re-check companion .java.
        String jmlContent = readFileFromDisk(uri);
        if (jmlContent == null) return;
        // Temporarily register the content so resolveCompanionJavaUri can parse it.
        lastContent.put(uri, jmlContent);
        String javaUri = resolveCompanionJavaUri(uri, jmlContent);
        lastContent.remove(uri);
        if (javaUri == null) return;
        String javaContent = lastContent.containsKey(javaUri)
                ? lastContent.get(javaUri) : readFileFromDisk(javaUri);
        if (javaContent == null) return;
        scheduleCheckNow(javaUri, javaContent);
    }

    /**
     * Called when a {@code .java} file is created or deleted on disk outside the editor.
     * Deleted files have their AST cache entry and diagnostics cleared.
     * Created files mark the nav cache dirty so the next navigation operation
     * or explicit index command re-runs the full project check.
     * Changed-but-not-open files are ignored — the user opens the file to trigger a check.
     */
    void handleWatchedJavaChange(String uri, FileChangeType type) {
        if (lastContent.containsKey(uri)) return;  // editor handles it
        if (type == FileChangeType.Deleted) {
            CheckRunner.getASTCache().remove(uri);
            if (client != null)
                client.publishDiagnostics(new PublishDiagnosticsParams(uri, List.of()));
        } else if (type == FileChangeType.Created) {
            // Mark nav cache dirty; the new file will be covered by the next project check.
            navCacheDirty = true;
        }
        // FileChangeType.Changed (not open): no action — let user open to trigger re-check
    }

    /**
     * Read the contents of a file identified by its LSP {@code file://} URI.
     * Returns {@code null} if the URI cannot be resolved or the file cannot be read.
     */
    private String readFileFromDisk(String uri) {
        String path = CheckRunner.uriToPath(uri);
        if (path == null) return null;
        try {
            return new String(java.nio.file.Files.readAllBytes(java.nio.file.Path.of(path)),
                    java.nio.charset.StandardCharsets.UTF_8);
        } catch (Exception e) {
            System.err.println("[OpenJML] readFileFromDisk failed for " + path + ": " + e);
            return null;
        }
    }

    // --- scheduling helpers ---

    /**
     * Given the URI of a {@code .jml} spec file and its current content, find the URI
     * of the companion {@code .java} source file.
     *
     * <p>Algorithm:
     * <ol>
     *   <li>Try the simple same-name replacement ({@code Foo.jml} → {@code Foo.java})
     *       in the same directory.  This covers the common case where spec-file names
     *       match their class names.</li>
     *   <li>If that file does not exist, parse {@code jmlContent} for the {@code package}
     *       declaration and the first {@code public}/{@code protected} class/interface/
     *       enum/record name.  Then search each root in {@code rootPaths} and
     *       {@code sourcePath} for {@code pkg/path/ClassName.java}.</li>
     * </ol>
     *
     * @param jmlUri     the URI of the {@code .jml} file
     * @param jmlContent the current content of the {@code .jml} file, or {@code null}
     *                   to read from disk
     * @return the URI of the companion {@code .java} file, or {@code null} if not found
     */
    private String resolveCompanionJavaUri(String jmlUri, String jmlContent) {
        // 1. Same-name replacement
        String simpleUri = jmlUri.substring(0, jmlUri.length() - 4) + ".java";
        String simplePath = CheckRunner.uriToPath(simpleUri);
        if (simplePath != null && new java.io.File(simplePath).exists()) return simpleUri;

        // 2. Parse content for package + class name
        String content = jmlContent;
        if (content == null) {
            String jmlPath = CheckRunner.uriToPath(jmlUri);
            if (jmlPath == null) return null;
            try { content = new String(java.nio.file.Files.readAllBytes(java.nio.file.Path.of(jmlPath))); }
            catch (Exception e) { return null; }
        }

        String pkg = null, cls = null;
        for (String line : content.split("\\n")) {
            if (pkg == null) {
                java.util.regex.Matcher m =
                        java.util.regex.Pattern.compile("^\\s*package\\s+([\\w.]+)\\s*;").matcher(line);
                if (m.find()) pkg = m.group(1);
            }
            if (cls == null) {
                java.util.regex.Matcher m =
                        java.util.regex.Pattern.compile(
                                "(?:public|protected)\\s+(?:(?:abstract|final|sealed|non-sealed)\\s+)*" +
                                "(?:class|interface|enum|record)\\s+(\\w+)").matcher(line);
                if (m.find()) cls = m.group(1);
            }
            if (pkg != null && cls != null) break;
        }
        if (cls == null) return null;

        String relPath = (pkg != null ? pkg.replace('.', java.io.File.separatorChar)
                                            + java.io.File.separator : "")
                         + cls + ".java";

        // Search workspace roots
        List<String> roots = new ArrayList<>(globalSettings.effectiveRoots());
        if (globalSettings.sourcePath != null && !globalSettings.sourcePath.isEmpty())
            java.util.Collections.addAll(roots,
                    globalSettings.sourcePath.split(java.io.File.pathSeparator));
        for (String root : roots) {
            java.nio.file.Path candidate = java.nio.file.Path.of(root).resolve(relPath);
            if (java.nio.file.Files.isRegularFile(candidate))
                return candidate.toUri().toString();
        }
        return null;
    }

    private void scheduleCheckNow(String uri, String content) {
        // Skip files that don't belong to any configured project (e.g. non-JML-natured
        // Eclipse projects, or files outside all workspace roots).
        OpenJMLSettings s = settingsForUri(uri);
        if (s == null) return;
        // .jml files are spec files; redirect check to companion .java
        if (uri.endsWith(".jml")) {
            String javaUri = resolveCompanionJavaUri(uri, content);
            if (javaUri == null) return;
            String javaContent = lastContent.get(javaUri);
            final String fJmlUri  = uri;
            final String fJavaUri = javaUri;
            final OpenJMLSettings fS = s;
            CompletableFuture<Void> cf = new CompletableFuture<>();
            lastCheckFuture.put(javaUri, cf);
            executor.submit(() -> {
                try {
                    runCheckContent(fJavaUri, javaContent, fS);  // javaContent may be null → reads from disk
                    verifyJmlCompanion(fJmlUri, fJavaUri);
                } finally {
                    cf.complete(null);
                }
            });
            return;
        }
        final OpenJMLSettings fS = s;
        CompletableFuture<Void> cf = new CompletableFuture<>();
        lastCheckFuture.put(uri, cf);
        executor.submit(() -> { try { runCheckContent(uri, content, fS); } finally { cf.complete(null); } });
    }

    /**
     * After a check triggered by opening/editing a {@code .jml} file, verify that
     * the {@code .java} AST's {@code specsCompilationUnit} points back to the same
     * {@code .jml} file.  A mismatch means the workspace has two competing spec
     * files for the same Java class (e.g. a hand-written {@code Foo.jml} alongside
     * a generated one found earlier on the specs path).
     *
     * @param jmlUri  the URI of the {@code .jml} file that triggered the check
     * @param javaUri the companion {@code .java} URI that was actually checked
     */
    private void verifyJmlCompanion(String jmlUri, String javaUri) {
        ASTCache.Entry entry = CheckRunner.getASTCache().get(javaUri);
        if (entry == null) return;
        JmlCompilationUnit specs = entry.ast().specsCompilationUnit;
        if (specs == null || specs == entry.ast() || specs.sourcefile == null) return;
        String actualJmlUri = specs.sourcefile.toUri().normalize().toString();
        if (!actualJmlUri.equals(jmlUri)) {
            clientError("OpenJML: .jml companion mismatch for " + javaUri
                    + ": opened " + jmlUri + " but the Java AST loaded specs from " + actualJmlUri
                    + " — there may be two competing spec files for the same class.");
        }
    }

    private void scheduleCheckFile(String uri) {
        // If the nav cache is clean, the project-wide check already covered all files
        // with current content.  Saves do not change in-memory content, so re-checking
        // here would only create a new IAPI context that invalidates the nav context.
        if (!navCacheDirty) return;
        // .jml files are spec files; redirect check to companion .java.
        // Use content-based check so companion diagnostics (including .jml markers) are updated.
        if (uri.endsWith(".jml")) {
            String javaUri = resolveCompanionJavaUri(uri, null);
            if (javaUri == null) return;
            String javaContent = lastContent.get(javaUri);
            if (javaContent != null) {
                executor.submit(() -> runCheckContent(javaUri, javaContent));
            } else {
                // java file not open; fall back to file-based check for java
                scheduleCheckFile(javaUri);
            }
            return;
        }
        // For .java files: use in-memory content if open, otherwise null (read from disk by OpenJML).
        // Both paths go through runCheckContent so dirty editors are always included.
        final String c = lastContent.get(uri);
        executor.submit(() -> runCheckContent(uri, c));
    }

    private void scheduleEscFile(String uri) {
        scheduleEscFile(uri, settingsForUri(uri));
    }


    private void scheduleEscFile(String uri, OpenJMLSettings s) {
        String content = lastContent.get(uri);
        if (content != null) {
            Map<String, String> snapshot = dirtySnapshot();
            submitEsc(uri, hook -> CheckRunner.escWithContext(uri, content, snapshot, s, hook,
                    methodDecl -> { markMethodCheckingByName(uri, methodDecl.name.toString()); executor.execute(() -> { publishMerged(uri); refreshCodeLenses(); }); }));
            return;
        }
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath == null) return;
        submitEsc(uri, hook -> CheckRunner.runEscFile(filePath, uri, s, hook,
                methodDecl -> { markMethodCheckingByName(uri, methodDecl.name.toString()); executor.execute(() -> { publishMerged(uri); refreshCodeLenses(); }); }));
    }


    private void startEscContent(String uri, String content) {
        Map<String, String> snapshot = dirtySnapshot();
        final OpenJMLSettings s = settingsForUri(uri);
        if (s == null) return;
        submitEsc(uri, hook -> CheckRunner.escWithContext(uri, content, snapshot, s, hook,
                methodDecl -> { markMethodCheckingByName(uri, methodDecl.name.toString()); executor.execute(() -> { publishMerged(uri); refreshCodeLenses(); }); }));
    }



    /**
     * Submit an ESC task for {@code uri}.
     *
     * <ul>
     *   <li>Cancels any running ESC task for the same URI.</li>
     *   <li>Marks all methods as CHECKING and requests a code-lens refresh.</li>
     *   <li>On completion, updates method statuses, publishes diagnostics, and
     *       refreshes code lenses.  Stale results from a superseded run are
     *       silently discarded via a generation counter.</li>
     * </ul>
     */
    private void submitEsc(String uri,
            java.util.function.Function<java.util.function.Consumer<IAPI>,
                                        CheckRunner.CheckResult> task) {
        // Cancel the previous ESC task for this URI (may not interrupt CPU-bound work,
        // but removes it from the task queue if it hasn't started yet).
        Future<?> prev = runningEscTasks.remove(uri);
        if (prev != null) prev.cancel(false);
        // Also kill any live z3 process for the previous task.
        IAPI prevApi = runningEscApis.remove(uri);
        if (prevApi != null) prevApi.cancelEsc();

        long myGen = escGen.computeIfAbsent(uri, k -> new AtomicLong()).incrementAndGet();
        // Reset all methods to UNKNOWN; each method will transition to CHECKING
        // individually as the prover starts it (via the onMethodStarted callback).
        markAllMethodStatus(uri, MethodStatus.UNKNOWN);
        refreshCodeLenses();

        Future<?> f = globalSettings.escPool.submit(() -> {
            try {
                // Hook fires inside CheckRunner once the fresh IAPI is created and
                // the ProofResultCollector is installed — before execute() is called.
                java.util.function.Consumer<IAPI> hook = api -> runningEscApis.put(uri, api);
                CheckRunner.CheckResult result = task.apply(hook);
                if (result.isCommandLineError())
                    System.err.println("[OpenJML] BUG: exit code 2 (bad command-line args) from ESC for " + uri);
                // Only publish if this task is still the latest for this URI.
                if (escGen.get(uri).get() == myGen) {
                    storeEscDiags(uri, result.diagnostics());
                    if (result.isInternalError()) {
                        System.err.println("[OpenJML] ESC internal error (exit code " + result.exitCode() + ")");
                        markAllMethodStatus(uri, MethodStatus.CHECK_ERROR);
                        refreshCodeLenses();
                    } else {
                        updateEscStatus(uri, result.diagnostics(), result.proofResults(), result.exitCode(),
                                            result.foreignMessages());
                    }
                    publishMerged(uri);
                }
            } catch (Throwable t) {
                System.err.println("[OpenJML] ESC failed: " + t);
                if (escGen.get(uri).get() == myGen) {
                    updateEscStatus(uri, List.of(), Map.of(), -1, List.of());
                    refreshCodeLenses();
                }
            } finally {
                runningEscApis.remove(uri);
                runningEscTasks.remove(uri);
            }
        });
        runningEscTasks.put(uri, f);
    }

    // --- runners (execute on the thread pool) ---

    // INVARIANT: the check runners below update checkDiags and publish merged
    // diagnostics, but they MUST NOT touch methodEscStatus or call
    // refreshCodeLenses().  Partially-typed code during editing must not disturb
    // the ESC code-lens status that the user sees.

    /**
     * Run a project-wide {@code --check --dirs} pass over all roots in
     * {@link OpenJMLSettings#effectiveRoots()}, supplying current in-memory
     * content as context.  All files are compiled in a single IAPI invocation
     * so their symbols share the same compilation context, enabling reliable
     * cross-file navigation (go-to-declaration, find-references, rename).
     *
     * <p>After the check completes, {@link #lastCheckedContent} is updated for
     * every currently-open file so that focus-triggered {@link #recheckUri}
     * calls (which skip files whose content is unchanged) become no-ops until
     * the next real edit.
     *
     * <p>If no roots are configured, falls back to a no-op (returns {@code false}).
     *
     * @return {@code true} if a project check was performed, {@code false} if
     *         no roots are configured and nothing was done
     */
    /**
     * Returns the subset of {@code allRoots} (OS paths) that are ancestors of
     * the given {@code uri}.  Falls back to {@code allRoots} if none match,
     * so a URI that does not sit under any known root still gets checked.
     */
    static List<String> rootsForUri(String uri, List<String> allRoots) {
        String filePath;
        try { filePath = java.net.URI.create(uri).getPath(); }
        catch (Exception e) { return allRoots; }
        List<String> matching = allRoots.stream()
                .filter(root -> {
                    String sep = java.io.File.separator;
                    String r = root.endsWith(sep) ? root : root + sep;
                    return filePath.startsWith(r);
                })
                .collect(java.util.stream.Collectors.toList());
        return matching.isEmpty() ? allRoots : matching;
    }

    private boolean runProjectCheck() {
        return runProjectCheck(globalSettings.effectiveRoots(), globalSettings);
    }

    private boolean runProjectCheck(List<String> roots) {
        return runProjectCheck(roots, globalSettings);
    }

    private boolean runProjectCheck(List<String> roots, OpenJMLSettings s) {
        if (roots.isEmpty()) return false;
        System.err.println("[runProjectCheck] roots=" + roots);
        Map<String, String> snapshot = dirtySnapshot();
        try {
            CheckRunner.DirCheckResult result =
                    CheckRunner.runCheckDirWithContext(roots, snapshot, s);
            result.diagnosticsByUri().forEach((diagUri, diags) -> {
                storeCheckDiags(diagUri, diags);
                publishMerged(diagUri);
            });
            // Mark every currently-open file as checked with its current content.
            // This suppresses redundant focus-triggered rechecks until the next edit.
            lastCheckedContent.putAll(snapshot);
            navCacheDirty = false;
            // Rebuild the nav declaration index from the nav-cache ASTs populated
            // by the project check.  All share one IAPI context so symbol identity
            // holds across files and cross-file navigation works correctly.
            CheckRunner.getASTCache().rebuildNavIndex();
            System.err.println("[runProjectCheck] nav cache now contains:");
            CheckRunner.getASTCache().forEachNav((u, e) -> System.err.println("[runProjectCheck]   " + u));
        } catch (Throwable t) {
            System.err.println("[runProjectCheck] error: " + t);
        }
        return true;
    }

    /**
     * Ensure the project-wide nav cache is up to date before a navigation
     * operation.  If {@link #navCacheDirty} is set, schedules a
     * {@link #runProjectCheck()} on the executor and returns a future that
     * completes when it finishes.  Otherwise completes immediately.
     */
    private CompletableFuture<Void> ensureNavCacheReady() {
        if (!navCacheDirty) return CompletableFuture.completedFuture(null);
        return CompletableFuture.runAsync(this::runProjectCheck, executor);
    }

    /**
     * Returns {@code true} if any currently-open document has in-memory content
     * that has not yet been processed by a completed {@code --check} pass.
     */
    private boolean isWorkspaceStale() {
        for (var entry : lastContent.entrySet()) {
            if (!entry.getValue().equals(lastCheckedContent.get(entry.getKey())))
                return true;
        }
        return false;
    }

    /**
     * Returns {@code true} if any file in the workspace currently has
     * ERROR-severity {@code --check} diagnostics (warnings are ignored).
     */
    private boolean hasWorkspaceErrors() {
        for (List<Diagnostic> diags : checkDiags.values()) {
            for (Diagnostic d : diags) {
                if (d.getSeverity() == org.eclipse.lsp4j.DiagnosticSeverity.Error)
                    return true;
            }
        }
        return false;
    }

    /**
     * Ensure the workspace is up to date, then ask the user to confirm if there
     * are errors.
     *
     * <ol>
     *   <li>If any open file is stale, run a blocking {@code --check} on
     *       {@code primaryUri} (which includes all open files via
     *       {@link CheckRunner#checkWithContext}).</li>
     *   <li>If any workspace file has ERROR-severity diagnostics, show a
     *       {@code window/showMessageRequest} dialog.  Returns {@code false}
     *       if the user cancels; {@code true} to proceed.</li>
     * </ol>
     *
     * @param primaryUri    the URI the operation is invoked on
     * @param operationName human-readable name for the dialog (e.g. "Rename")
     * @return a future completing with {@code true} to proceed, {@code false} to abort
     */
    private CompletableFuture<Boolean> ensureFreshAndConfirm(
            String primaryUri, String operationName) {
        CompletableFuture<Void> checkFuture;
        if (navCacheDirty) {
            checkFuture = CompletableFuture.runAsync(() -> {
                OpenJMLSettings s = settingsForUri(primaryUri);
                if (s == null) { System.err.println("[ensureFreshAndConfirm] no project for " + primaryUri); return; }
                List<String> roots = rootsForUri(primaryUri, s.effectiveRoots());
                System.err.println("[ensureFreshAndConfirm] op=" + operationName
                        + " uri=" + primaryUri + " roots=" + roots);
                if (!runProjectCheck(roots, s)) {
                    System.err.println("[ensureFreshAndConfirm] no roots — falling back to single-file check");
                    // No roots configured: fall back to single-file check.
                    String content = lastContent.get(primaryUri);
                    if (content != null) runCheckContent(primaryUri, content);
                }
            }, executor);
        } else {
            checkFuture = CompletableFuture.completedFuture(null);
        }

        return checkFuture.thenCompose(v -> {
            if (!hasWorkspaceErrors())
                return CompletableFuture.completedFuture(true);
            if (client == null)
                return CompletableFuture.completedFuture(true);

            ShowMessageRequestParams req = new ShowMessageRequestParams();
            req.setType(MessageType.Warning);
            req.setMessage(operationName + " may be inaccurate because the workspace"
                    + " has compilation errors. Proceed anyway?");
            MessageActionItem proceed = new MessageActionItem("Proceed Anyway");
            MessageActionItem cancel  = new MessageActionItem("Cancel");
            req.setActions(List.of(proceed, cancel));

            return client.showMessageRequest(req).thenApply(action ->
                    action != null && "Proceed Anyway".equals(action.getTitle()));
        });
    }

    private void runCheckContent(String uri, String content) {
        OpenJMLSettings s = settingsForUri(uri);
        if (s == null) return;
        runCheckContent(uri, content, s);
    }

    private void runCheckContent(String uri, String content, OpenJMLSettings s) {
        // .jml files are spec files; should not be passed to OpenJML on command line.
        // scheduleCheckNow redirects to the companion .java, but guard here as well.
        if (uri.endsWith(".jml")) return;
        if (content != null) lastCheckedContent.put(uri, content);
        try {
            // Snapshot lastContent at execution time so that concurrent edits do not
            // mutate the context map while OpenJML is parsing it.
            Map<String, String> snapshot = dirtySnapshot();
            CheckRunner.CheckResult result = CheckRunner.checkWithContext(
                    uri, content, snapshot, s);
            // Publish diagnostics for all compiled files (primary + companions) uniformly.
            result.allDiagnostics().forEach((diagUri, diags) -> {
                storeCheckDiags(diagUri, diags);
                publishMerged(diagUri);
                String c = lastContent.get(diagUri);
                if (c != null) lastCheckedContent.put(diagUri, c);
            });
            // If allDiagnostics is empty (non-context check), fall back to primary.
            if (result.allDiagnostics().isEmpty()) {
                storeCheckDiags(uri, result.diagnostics());
                publishMerged(uri);
            }
            // Do NOT call refreshCodeLenses() here.
        } catch (Throwable t) {
            System.err.println("[OpenJML] check failed for " + uri + ": " + t);
        }
    }


    // --- ESC code-lens status helpers ---

    /** Set all detected methods in {@code uri} to the given {@code status}. */
    private void markAllMethodStatus(String uri, MethodStatus status) {
        String content = lastContent.get(uri);
        if (content == null) return;
        List<JavaSourceScanner.MethodInfo> methods = JavaSourceScanner.findMethods(content);
        if (methods.isEmpty()) return;
        Map<Integer, MethodStatus> statuses = new HashMap<>();
        for (JavaSourceScanner.MethodInfo m : methods) {
            statuses.put(m.startLine(), status);
        }
        methodEscStatus.put(uri, statuses);
    }

    /** Mark all detected methods in {@code uri} as currently being checked. */
    /**
     * Set the code lens status for a single method (identified by simple name)
     * to CHECKING, then refresh code lenses.  Called when the prover sends a
     * RUNNING notification for that method so the lens updates before the result
     * arrives.  If multiple overloaded methods share the name, all are marked.
     */
    private void markMethodCheckingByName(String uri, String methodName) {
        String content = lastContent.get(uri);
        if (content == null) return;
        // Create a new map (same pattern as updateEscStatusPartial) so the updated
        // entry is published to the ConcurrentHashMap with a proper memory barrier,
        // making it visible to the LSP handler thread when it responds to codeLens requests.
        Map<Integer, MethodStatus> current =
                new HashMap<>(methodEscStatus.getOrDefault(uri, Map.of()));
        boolean changed = false;
        for (JavaSourceScanner.MethodInfo m : JavaSourceScanner.findMethods(content)) {
            if (m.name().equals(methodName)) {
                current.put(m.startLine(), MethodStatus.CHECKING);
                changed = true;
            }
        }
        if (changed) {
            methodEscStatus.put(uri, current);
            refreshCodeLenses();
        }
    }

    private void markEscChecking(String uri) {
        markAllMethodStatus(uri, MethodStatus.CHECKING);
        refreshCodeLenses();
    }

    /**
     * Update per-method ESC status for {@code uri}.
     *
     * <p>Exit codes: 0 = success (UNSAT/INFEASIBLE expected), 1 = syntax/type
     * errors (CHECK_ERROR for any method with no proof result), 6 = verification
     * failures (SAT/POSSIBLY_SAT/SKIPPED/TIMEOUT/CANCELLED/UNKNOWN/ERROR).
     */
    private void updateEscStatus(String uri, List<Diagnostic> diags,
                                 Map<String, IProverResult.Kind> proofResults, int exitCode,
                                 List<String> foreignFiles) {
        String content = lastContent.get(uri);
        if (content == null) return;
        // ESC always produces an attributed AST which is stored in the cache, so
        // AST-based discovery is always available here.  Regex fallback is not needed.
        ASTCache.Entry astEntry = CheckRunner.getASTCache().get(uri);
        if (astEntry == null) {
            System.err.println("[OpenJML] updateEscStatus: no AST for " + uri + " — skipping");
            return;
        }
        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(astEntry.ast(), content);
        if (methods.isEmpty()) return;

        boolean hasForeignErrors = !foreignFiles.isEmpty();
        Map<Integer, MethodStatus> statuses = new HashMap<>();
        for (JavaSourceScanner.MethodInfo m : methods) {
            IProverResult.Kind kind = CheckRunner.lookupResult(proofResults, m.rawName());
            statuses.put(m.startLine(),
                    proofResultToStatus(kind, diags, m.startLine(), m.endLine(),
                                        exitCode, hasForeignErrors));
        }
        methodEscStatus.put(uri, statuses);
        addVerifiedDiagnostics(uri, proofResults, null);
        refreshCodeLenses();

        if (hasForeignErrors) {
            String fileName = uri.substring(uri.lastIndexOf('/') + 1);
            clientWarn("OpenJML: ESC on " + fileName
                    + " could not run — type errors in: " + String.join(", ", foreignFiles));
        }
    }

    /**
     * For each method in {@code uri} whose proof result is UNSAT (verified),
     * append a Hint-severity diagnostic at the method-name token so that the
     * Eclipse client can attach a green {@code ESCInfoAnnotation} marker there.
     *
     * <p>The diagnostic range spans the method name on the declaration line.
     * The source is {@link DiagnosticConverter#SOURCE_ESC} so it is routed to
     * the ESC marker type ({@code JMLESCProblem}) by {@code OpenJMLLanguageClient}.
     */
    /**
     * Add Verified (Hint) diagnostics for methods that appear in {@code proofResults}
     * with {@link IProverResult#UNSAT}.
     *
     * <p>When {@code target} is non-null (per-method run) only the marker for that
     * specific method is removed and replaced, leaving other methods' Verified markers
     * intact.  When {@code target} is null (whole-file run) all existing Verified
     * markers are cleared before adding the new set.
     */
    private void addVerifiedDiagnostics(String uri,
                                        Map<String, IProverResult.Kind> proofResults,
                                        JavaSourceScanner.MethodInfo target) {
        String content = lastContent.get(uri);
        if (content == null || proofResults.isEmpty()) return;
        String[] lines = content.split("\n", -1);

        ASTCache.Entry astEntry = CheckRunner.getASTCache().get(uri);
        if (astEntry == null) return;
        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(astEntry.ast(), content);

        List<Diagnostic> verified = new ArrayList<>();
        for (JavaSourceScanner.MethodInfo m : methods) {
            // For per-method runs consider only the target method.
            if (target != null && m.startLine() != target.startLine()) continue;
            // Use rawName() for the proof-result lookup: FQN+sig key from AST, bare name
            // from regex fallback. lookupResult() handles both cases.
            if (CheckRunner.lookupResult(proofResults, m.rawName()) != IProverResult.UNSAT) continue;
            int line = m.startLine();   // 0-based
            if (line >= lines.length) continue;
            String lineText = lines[line];
            // For constructors m.name() is the class name; for methods it is the method name.
            // Both appear on the declaration line, so indexOf finds the right token.
            int col = lineText.indexOf(m.name());
            if (col < 0) col = 0;
            int endCol = col + m.name().length();
            System.out.println("[OpenJML] Verified marker: method=" + m.name()
                    + " rawName=" + m.rawName()
                    + " line=" + line + " col=" + col + " endCol=" + endCol
                    + " lineText='" + lineText.stripTrailing() + "'");
            Range range = new Range(new Position(line, col), new Position(line, endCol));
            Diagnostic d = new Diagnostic(range, "Verified",
                    DiagnosticSeverity.Hint, DiagnosticConverter.SOURCE_ESC);
            verified.add(d);
        }

        List<Diagnostic> existing = new ArrayList<>(escDiags.getOrDefault(uri, List.of()));
        if (target != null) {
            // Per-method: remove only the Verified marker within this method's line range.
            existing.removeIf(d -> DiagnosticSeverity.Hint.equals(d.getSeverity())
                    && DiagnosticConverter.SOURCE_ESC.equals(d.getSource())
                    && target.contains(d.getRange().getStart().getLine()));
        } else {
            // Whole-file: replace all Verified markers.
            existing.removeIf(d -> DiagnosticSeverity.Hint.equals(d.getSeverity())
                    && DiagnosticConverter.SOURCE_ESC.equals(d.getSource()));
        }
        existing.addAll(verified);
        escDiags.put(uri, existing);
    }

    /**
     * Update per-method ESC status for {@code uri} using a <em>partial</em> proof-result
     * snapshot produced mid-run.  Only methods that already have a proof result are
     * updated; methods not yet proven retain their current status (typically CHECKING).
     *
     * <p>This is called from the per-method callback inside {@link CheckRunner#runEscDirWithContext}
     * so that code lenses flip from ⧗ Checking… to their final state as each proof
     * finishes, rather than all at once when the entire file completes.
     *
     * @param uri                 document URI
     * @param diags               diagnostics accumulated so far (used for issue count)
     * @param partialProofResults proof results for methods that have finished so far
     */
    private void updateEscStatusPartial(String uri, List<Diagnostic> diags,
            Map<String, IProverResult.Kind> partialProofResults) {
        String content = lastContent.get(uri);
        if (content == null) return;
        ASTCache.Entry astEntry = CheckRunner.getASTCache().get(uri);
        if (astEntry == null) return;
        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(astEntry.ast(), content);
        if (methods.isEmpty()) return;
        Map<Integer, MethodStatus> current = new HashMap<>(
                methodEscStatus.getOrDefault(uri, Map.of()));
        for (JavaSourceScanner.MethodInfo m : methods) {
            IProverResult.Kind kind = CheckRunner.lookupResult(partialProofResults, m.rawName());
            if (kind == null) continue;   // not yet proven — leave as CHECKING or UNKNOWN
            // exitCode=0: the run is in progress; kind != null so exitCode is not used
            // by proofResultToStatus (null-kind is the only path that reads exitCode).
            current.put(m.startLine(),
                    proofResultToStatus(kind, diags, m.startLine(), m.endLine(), 0, false));
        }
        methodEscStatus.put(uri, current);
    }

    /**
     * Convert a proof result kind to a {@link MethodStatus}.
     *
     * @param kind            proof result kind, or {@code null} if none was recorded
     * @param diags           all diagnostics from the ESC run (used for issue count)
     * @param start           first line of the method (inclusive)
     * @param end             last line of the method (inclusive)
     * @param exitCode        OpenJML exit code: 0=ok, 1=syntax/type errors, 6=verification failures
     * @param hasForeignErrors true when errors in other files (not the focus file) caused the failure
     */
    private static MethodStatus proofResultToStatus(IProverResult.Kind kind,
                                                     List<Diagnostic> diags,
                                                     int start, int end, int exitCode,
                                                     boolean hasForeignErrors) {
        if (kind == IProverResult.UNSAT) {
            return MethodStatus.VERIFIED;
        } else if (kind == IProverResult.INFEASIBLE) {
            return MethodStatus.INFEASIBLE;
        } else if (kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT
                || kind == IProverResult.UNKNOWN || kind == IProverResult.ERROR) {
            long issues = diags.stream()
                    .filter(d -> { int l = d.getRange().getStart().getLine(); return l >= start && l <= end; })
                    .count();
            return MethodStatus.notVerified((int) Math.max(kind == IProverResult.SAT
                    || kind == IProverResult.POSSIBLY_SAT ? 1 : 0, issues));
        } else if (kind == IProverResult.TIMEOUT) {
            return MethodStatus.TIMEOUT;
        } else if (kind == IProverResult.CANCELLED) {
            return MethodStatus.CANCELLED;
        } else if (kind == IProverResult.SKIPPED) {
            return MethodStatus.SKIPPED;
        } else {
            // null: no proof result recorded.
            // exitCode 1 means syntax/type errors prevented ESC.
            // Distinguish: errors in the focus file vs. errors only in other files.
            if (exitCode == 1) {
                return hasForeignErrors ? MethodStatus.CHECK_ERROR_DEPS : MethodStatus.CHECK_ERROR;
            }
            return MethodStatus.UNKNOWN;
        }
    }

    private void refreshCodeLenses() {
        if (client != null) client.refreshCodeLenses();
    }

    // --- diagnostic merging ---

    /**
     * Publish {@code diags} to the client for {@code uri} and update {@link #markedUris}.
     *
     * <p>All diagnostic publications must go through this method (never call
     * {@code client.publishDiagnostics} directly) so that {@link #markedUris} stays
     * accurate and {@link #clearMarkers} can clear every URI that holds markers.
     *
     * <p>An empty list removes {@code uri} from {@link #markedUris}; a non-empty
     * list adds it.
     */
    // --- client console logging helpers ---

    /** Send an Info-level message to the client (shown timestamped in the JML Console). */
    private void clientLog(String message) {
        if (client == null) return;
        client.logMessage(new MessageParams(MessageType.Info, message));
    }

    /** Send a Warning-level message to the client (shown timestamped in the JML Console). */
    private void clientWarn(String message) {
        if (client == null) return;
        client.logMessage(new MessageParams(MessageType.Warning, message));
    }

    /** Send an Error-level message to the client (shown timestamped in the JML Console). */
    private void clientError(String message) {
        if (client == null) return;
        client.logMessage(new MessageParams(MessageType.Error, message));
    }

    private void publishDiags(String uri, List<Diagnostic> diags) {
        if (client == null) return;
        client.publishDiagnostics(new PublishDiagnosticsParams(uri, diags));
        if (diags.isEmpty()) markedUris.remove(uri);
        else                 markedUris.add(uri);
    }

    /**
     * Store ESC diagnostics for {@code uri}, clearing any stale {@code --check}
     * results.  ESC subsumes check (it performs all the same type and annotation
     * checks), so check diagnostics are no longer useful once ESC has run.
     * An empty {@code diags} list removes both stores.
     */
    private void storeEscDiags(String uri, List<Diagnostic> diags) {
        checkDiags.remove(uri);
        if (diags.isEmpty()) escDiags.remove(uri);
        else                 escDiags.put(uri, diags);
    }

    /**
     * Store {@code --check} diagnostics for {@code uri}, retaining only ESC
     * <em>verification failures</em> from any previous ESC run.  Check-level
     * ESC diagnostics (type errors, annotation errors also caught by
     * {@code --check}) are dropped so that the fresh check result is authoritative
     * for those categories.  ESC proof-failure diagnostics are kept because they
     * represent information {@code --check} cannot produce.
     */
    private void storeCheckDiags(String uri, List<Diagnostic> diags) {
        List<Diagnostic> prev = escDiags.get(uri);
        if (prev != null && !prev.isEmpty()) {
            List<Diagnostic> kept = prev.stream()
                    .filter(DiagnosticConverter::isEscVerificationFailure)
                    .collect(java.util.stream.Collectors.toList());
            if (kept.isEmpty()) escDiags.remove(uri);
            else                escDiags.put(uri, kept);
        }
        checkDiags.put(uri, diags);
    }

    private void publishMerged(String uri) {
        List<Diagnostic> merged = new ArrayList<>();
        merged.addAll(checkDiags.getOrDefault(uri, List.of()));
        merged.addAll(escDiags.getOrDefault(uri, List.of()));
        merged.addAll(racDiags.getOrDefault(uri, List.of()));
        publishDiags(uri, merged);
    }


    // --- debounce / cancel helpers ---

    private void debounce(Map<String, ScheduledFuture<?>> map, String uri,
                          Runnable task, long delayMs) {
        ScheduledFuture<?> prev = map.put(uri,
                scheduler.schedule(() -> {
                    map.remove(uri);
                    executor.submit(task);
                }, delayMs, TimeUnit.MILLISECONDS));
        if (prev != null) prev.cancel(false);
    }

    private void cancelPending(String uri) {
        ScheduledFuture<?> c = pendingCheck.remove(uri);
        if (c != null) c.cancel(false);
        ScheduledFuture<?> e = pendingEsc.remove(uri);
        if (e != null) e.cancel(false);
    }

    /**
     * Abort only the currently-running method proof for the given target, then
     * allow the ESC loop to continue with the next method.  Same target format as
     * {@link #cancelEsc(String)}, but calls {@link org.openjml.IAPI#abortCurrentProof()}
     * instead of {@link org.openjml.IAPI#cancelEsc()}, so the ESC run is not terminated.
     */
    void abortCurrentProof(String target) {
        if (target != null && target.contains("#")) {
            abortCurrentProofForMethodKey(target);
        } else if (target != null && !target.isEmpty()) {
            abortCurrentProofForUri(target);
        } else {
            new ArrayList<>(runningEscTasks.keySet()).forEach(this::abortCurrentProofForUri);
            new ArrayList<>(runningEscMethodTasks.keySet()).forEach(this::abortCurrentProofForMethodKey);
        }
    }

    private void abortCurrentProofForUri(String uri) {
        IAPI api = runningEscApis.get(uri);
        if (api != null) api.abortCurrentProof();
    }

    private void abortCurrentProofForMethodKey(String methodKey) {
        // Try the per-method task first (the method was submitted as its own ESC run).
        IAPI api = runningEscMethodApis.get(methodKey);
        if (api != null) {
            System.out.println("[OpenJML] abortCurrentProof: found per-method API for " + methodKey);
            api.abortCurrentProof();
            return;
        }
        // Fall back to the file-level task that contains this method (e.g. split-by-file
        // or runEsc on the whole file).  Abort only the current proof so the remaining
        // methods in that file continue to be proved.
        String uri = methodKey.contains("#") ? methodKey.substring(0, methodKey.indexOf('#')) : null;
        if (uri != null) {
            IAPI fileApi = runningEscApis.get(uri);
            if (fileApi != null) {
                System.out.println("[OpenJML] abortCurrentProof: found file-level API for uri=" + uri);
                fileApi.abortCurrentProof();
            } else {
                System.out.println("[OpenJML] abortCurrentProof: NO API found for uri=" + uri
                        + "; runningEscApis keys=" + runningEscApis.keySet());
            }
        }
    }

    /**
     * Cancel a specific running ESC task, or all running ESC tasks.
     * Also kills the in-progress SMT solver process via
     * {@link org.openjml.IAPI#cancelEsc()} so the ESC thread is unblocked
     * immediately rather than waiting for the current solver query to complete.
     *
     * <p>Cancellation granularity:
     * <ul>
     *   <li>{@code target == null} or empty — cancel all per-file and per-method tasks.</li>
     *   <li>{@code target} is a bare URI — cancel the whole-file run for that file.</li>
     *   <li>{@code target} contains {@code '#'} (format {@code "uri#methodName"}) —
     *       cancel only that specific method's run.</li>
     * </ul>
     */
    void cancelEsc(String target) {
        if (target != null && target.contains("#")) {
            abortEscForMethodKey(target);
        } else if (target != null && !target.isEmpty()) {
            abortEscForUri(target);
        } else {
            new ArrayList<>(runningEscTasks.keySet()).forEach(this::abortEscForUri);
            new ArrayList<>(runningEscMethodTasks.keySet()).forEach(this::abortEscForMethodKey);
        }
    }

    private void abortEscForUri(String uri) {
        Future<?> f = runningEscTasks.remove(uri);
        // cancel(false): prevent a queued task from starting, but do NOT interrupt
        // a running thread.  Thread interruption causes SolverProcess sleeps to throw
        // "sleep interrupted" which surfaces as an ERROR diagnostic rather than CANCELLED.
        // The actual kill is handled by api.cancelEsc() below (destroyForcibly).
        if (f != null) f.cancel(false);
        IAPI api = runningEscApis.remove(uri);
        if (api != null) {
            int k = uri.lastIndexOf('/');
            String name = k == -1 ? uri : uri.substring(k+1);
            System.err.println("[OpenJML] ESC cancelled for " + name);
            api.cancelEsc();
        } else if (f != null) {
            int k = uri.lastIndexOf('/');
            String name = k == -1 ? uri : uri.substring(k+1);
            System.err.println("[OpenJML] ESC task cancelled (queued, not yet running) for " + name);
        }
    }

    private void abortEscForMethodKey(String methodKey) {
        Future<?> f = runningEscMethodTasks.remove(methodKey);
        if (f != null) f.cancel(false);
        IAPI api = runningEscMethodApis.remove(methodKey);
        if (api != null) {
            int k = methodKey.lastIndexOf('/');
            String name = k == -1 ? methodKey : methodKey.substring(k+1);
            System.err.println("[OpenJML] ESC cancelled for " + name);
            api.cancelEsc();
        } else if (f != null) {
            int k = methodKey.lastIndexOf('/');
            String name = k == -1 ? methodKey : methodKey.substring(k+1);
            System.err.println("[OpenJML] ESC task cancelled (queued, not yet running) for " + name);
        }
    }

    /**
     * Returns a snapshot of all currently-running ESC task keys.
     * Whole-file runs are identified by bare URI; per-method runs use
     * {@code "uri#methodName"} format.
     */
    List<String> getRunningEscUris() {
        List<String> result = new ArrayList<>(runningEscTasks.keySet());
        result.addAll(runningEscMethodTasks.keySet());
        return List.copyOf(result);
    }

    /**
     * Clear all OpenJML diagnostic markers without scheduling any new checks.
     *
     * <p>Clears {@code checkDiags}, {@code escDiags}, {@code racDiags}, and
     * {@code methodEscStatus}, then publishes empty diagnostic lists for every
     * open file so the client removes the markers immediately.  Code lenses are
     * refreshed so per-method ESC status indicators reset to the idle state.
     *
     * <p>Pending and running checks are left undisturbed — they will overwrite
     * the now-empty markers when they complete.  Use {@link #resetAndReindex()}
     * instead when a full restart is needed.
     */
    void clearMarkers() {
        checkDiags.clear();
        escDiags.clear();
        racDiags.clear();
        methodEscStatus.clear();
        // Snapshot markedUris before clearing so we don't modify the set while iterating.
        List<String> toClean = new ArrayList<>(markedUris);
        markedUris.clear();
        for (String uri : toClean) {
            if (client != null) client.publishDiagnostics(new PublishDiagnosticsParams(uri, List.of()));
        }
        refreshCodeLenses();
    }

    /**
     * Clear all in-memory caches and restart as if the server had just started,
     * then re-index the workspace from disk.
     *
     * <p>Cancels any pending check/ESC work, clears the AST cache, diagnostic
     * maps, and ESC status, and publishes empty diagnostics for all previously
     * marked URIs.  Then schedules a fresh workspace index pass from disk via
     * {@link #scheduleWorkspaceReindex()}.
     *
     * <p><b>Open-file content</b>: the server does <em>not</em> re-check files
     * from its cached {@code lastContent} map.  That content may be stale or
     * out-of-sync with the editor (which is often the reason the reset was
     * requested in the first place).  Clients must follow the reset with fresh
     * content using one of these protocols:
     * <ol>
     *   <li><b>Save-then-clear</b>: save all open editors before issuing
     *       {@code clearAndReindex}; the workspace index picks up the saved
     *       content from disk.</li>
     *   <li><b>Clear-then-resend</b>: issue {@code clearAndReindex} then send a
     *       full-text {@code textDocument/didChange} for every dirty open editor
     *       in JML-natured projects (both {@code .java} and {@code .jml} files).
     *       The {@code didChange} must carry the complete current buffer text, not
     *       an incremental delta.</li>
     * </ol>
     * In both cases the client may optionally send
     * {@code workspace/didChangeConfiguration} with updated project configuration
     * alongside the {@code clearAndReindex} command; the server rebuilds its
     * project registry from the current {@code globalSettings.projects} immediately
     * during the reset so that the disk scan always uses valid settings.
     *
     * <p>Intended as a recovery command when the user suspects the server state
     * has become stale or is consuming too much memory.  When the server process
     * itself is restarted (e.g., because the executable path changed), it goes
     * through the normal {@code initialize}/{@code initialized} flow, which calls
     * {@link #scheduleWorkspaceReindex()} via the same path.
     */
    void resetAndReindex() {
        // Cancel all pending debounced and running work.
        pendingCheck.values().forEach(f -> f.cancel(false));
        pendingCheck.clear();
        pendingEsc.values().forEach(f -> f.cancel(false));
        pendingEsc.clear();
        ScheduledFuture<?> pcp = pendingCheckPaths;
        if (pcp != null) { pcp.cancel(false); pendingCheckPaths = null; }
        cancelEsc(null);  // cancel futures and abort any live z3 processes
        lastCheckFuture.clear();

        // Clear all diagnostic and status caches.
        checkDiags.clear();
        escDiags.clear();
        racDiags.clear();
        methodEscStatus.clear();
        lastCheckedContent.clear();
        // Clear the dirty-file set so that the subsequent workspace index reads
        // all files from disk rather than serving stale in-memory editor content.
        // The client is responsible for re-sending didChange for dirty editors
        // after the reset; that will repopulate dirtyUris with fresh content.
        dirtyUris.clear();
        // Clear the editor content cache.  Stale/orphan entries (files closed or
        // renamed without the server being notified) would otherwise accumulate.
        // didSave and didClose use remove(), which is a no-op on a missing key,
        // so they are unaffected.  The client repopulates via fresh didOpen/didChange.
        lastContent.clear();
        // Clear and immediately repopulate the per-project settings registry from
        // the current globalSettings.projects.  This ensures settingsForUri() continues
        // to work during the subsequent disk scan and after any client-sent
        // didChange notifications.  The client may send a fresh
        // workspace/didChangeConfiguration to override these settings.
        updateProjectSettings(globalSettings.projects);

        // Clear the AST cache (both tiers and declaration indexes).
        CheckRunner.getASTCache().clear();
        // Mark nav cache dirty so the next Rename/FindReferences triggers a fresh project check.
        navCacheDirty = true;

        // Publish empty diagnostics for all marked URIs so stale markers disappear.
        List<String> toClean = new ArrayList<>(markedUris);
        markedUris.clear();
        for (String uri : toClean) {
            publishDiags(uri, List.of());
        }
        clientLog("OpenJML: caches cleared — re-indexing workspace from disk. "
                + "Send full-text didChange for any dirty open editors to restore their diagnostics.");

        // Re-index all configured projects from disk.
        // Do NOT re-check from lastContent: that content may be the stale/corrupted
        // state that prompted this reset.  The client is responsible for re-sending
        // current editor content via fresh didChange notifications.
        scheduleWorkspaceReindex();

        refreshCodeLenses();
    }

    /**
     * Schedule a workspace index pass from disk for all configured projects.
     *
     * <p>Each project is indexed separately so that per-project AST cache
     * sections are populated correctly for {@code workspace/symbol} filtering.
     * This is the shared entry point used by both {@link #resetAndReindex()} and
     * the {@code initialized} notification handler, ensuring both paths go through
     * the same indexing logic.
     */
    void scheduleWorkspaceReindex() {
        if (globalSettings.projects != null && !globalSettings.projects.isEmpty()) {
            for (OpenJMLSettings.ProjectConfig cfg : globalSettings.projects) {
                indexProject(cfg.id);
            }
        } else {
            indexProject(null);
        }
    }

    /**
     * Index the source directories of the specified project (or all projects
     * when {@code projectId} is null or empty) by scheduling a {@code --check}
     * pass.  This rebuilds the declaration index used by
     * {@code workspace/symbol} without clearing existing diagnostics or the
     * AST cache.
     */
    void indexProject(String projectId) {
        List<String> sourceDirs = new ArrayList<>();

        if (globalSettings.projects != null && !globalSettings.projects.isEmpty()) {
            for (OpenJMLSettings.ProjectConfig cfg : globalSettings.projects) {
                if (projectId == null || projectId.isEmpty() || projectId.equals(cfg.id)) {
                    if (cfg.rootPaths != null) sourceDirs.addAll(cfg.rootPaths);
                }
            }
        }

        if (sourceDirs.isEmpty()) {
            clientLog("OpenJML: no source directories configured — cannot index project.");
            return;
        }

        navCacheDirty = true;
        OpenJMLSettings s = settingsForProject(projectId);
        List<String> roots = List.copyOf(sourceDirs);
        executor.submit(() -> runProjectCheck(roots, s));
    }

    /** Shut down all executor services. Called from the language server's shutdown sequence. */
    void shutdown() {
        scheduler.shutdownNow();
        executor.shutdownNow();
    }
}
