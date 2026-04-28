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
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.openjml.IAPI;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
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
import java.util.concurrent.atomic.AtomicBoolean;
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
 * </ul>
 * ESC is never triggered automatically on open — only on save (per the setting)
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

    // --- session and proof-result helpers ---

    private static String methodKey(String uri, JavaSourceScanner.MethodInfo m) {
        return uri + "#" + m.rawName();
    }

    /** Status-only update. For same gen: preserves existing byUri. For new gen: clears byUri. */
    private void storeProofResult(String key, long gen, MethodStatus status, String projectId) {
        proofResults.compute(key, (k, existing) -> {
            if (existing != null && existing.gen() > gen) return existing;
            Map<String, List<Diagnostic>> keepByUri =
                (existing != null && existing.gen() == gen) ? existing.byUri() : Map.of();
            return new ProofResult(k, gen, status, keepByUri, projectId);
        });
    }

    /** Full update: always uses the provided byUri (for final proof results). */
    private void storeProofResult(String key, long gen, MethodStatus status,
                                   Map<String, List<Diagnostic>> byUri, String projectId) {
        proofResults.compute(key, (k, existing) -> {
            if (existing != null && existing.gen() > gen) return existing;
            return new ProofResult(k, gen, status, byUri, projectId);
        });
    }

    private boolean isCurrentSession(String scopeKey, long gen) {
        RunningSession s = runningSessions.get(scopeKey);
        return s != null && s.sessionGen() == gen;
    }

    private final OpenJMLSettings globalSettings;
    private final String codeLensCommand;
    private LanguageClient client;
    private boolean clientSupportsSemanticTokenRefresh = false;

    /**
     * Set to {@code true} when the client declared {@code supportsActionMessages: true}
     * in {@code initializationOptions}.  When true, advisory and error messages are
     * sent via {@code $/openjml/actionMessage} instead of {@code window/logMessage}.
     */
    private boolean clientSupportsActionMessages = false;
    /** Messages for which a dialog has already been shown this session; console logs still repeat. */
    private final java.util.Set<String> shownDialogMessages =
            java.util.Collections.newSetFromMap(new java.util.concurrent.ConcurrentHashMap<>());

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

    /** Monotonic counter: incremented once per proof session at source-read time. */
    private final AtomicLong sessionCounter = new AtomicLong();

    /** Proof result per method, keyed by uri+"#"+rawMethodName. */
    record ProofResult(String methodKey, long gen, MethodStatus status,
                       Map<String, List<Diagnostic>> byUri, String projectId) {}
    private final ConcurrentHashMap<String, ProofResult> proofResults = new ConcurrentHashMap<>();

    /** Tracks an in-progress ESC task: its session gen, the Future, and the IAPI (set after start). */
    record RunningSession(long sessionGen, Future<?> future, java.util.concurrent.atomic.AtomicReference<IAPI> api, boolean visible, String projectId) {
    }
    /** Running ESC sessions keyed by uri (file runs) or uri+"#"+rawMethodName (per-method runs) or "batch:"+n (batch runs). */
    private final ConcurrentHashMap<String, RunningSession> runningSessions = new ConcurrentHashMap<>();

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
     * Per-project dirty flags for the nav (declaration) cache.
     * An absent entry is treated as dirty (true).  Populated eagerly on
     * {@link #initProjectNavState()} so that {@link #didChange} can set the
     * flag without a ConcurrentHashMap lookup on the hot path.
     */
    private final ConcurrentHashMap<String, AtomicBoolean> projectNavDirty = new ConcurrentHashMap<>();

    /** One monitor object per project — held for the entire check+rebuild cycle. */
    private final ConcurrentHashMap<String, Object> projectNavLocks = new ConcurrentHashMap<>();

    /**
     * Dirty flag for the project that owns the currently focused editor.
     * Set once in {@link #didOpen}; used directly (no lookup) in {@link #didChange}.
     * Never null: falls back to {@link #NOOP_DIRTY} for files outside any project.
     */
    private AtomicBoolean currentNavDirty = NOOP_DIRTY;

    /** Sentinel used when the focused file belongs to no configured project. */
    private static final AtomicBoolean NOOP_DIRTY = new AtomicBoolean(false);

    /**
     * @param globalSettings  shared settings object
     * @param codeLensCommand the command name to embed in code-lens actions (e.g. run ESC for method)
     */
    public OpenJMLTextDocumentService(OpenJMLSettings globalSettings, String codeLensCommand) {
        this.globalSettings = globalSettings;
        this.codeLensCommand = codeLensCommand;
    }

    /** Called by {@link org.openjml.lsp.OpenJMLLanguageServer} after reading initializationOptions. */
    public void setClientSupportsActionMessages(boolean supports) {
        this.clientSupportsActionMessages = supports;
    }

    public void setClientRefreshCapabilities(boolean semanticTokens) {
        this.clientSupportsSemanticTokenRefresh = semanticTokens;
    }

    /** Called by {@link OpenJMLLanguageServer} when the client connects; wires log and warning callbacks. */
    public void connect(LanguageClient client) {
        this.client = client;
        CheckRunner.setLogCallback(msg -> {
            if (client != null)
                client.logMessage(new MessageParams(MessageType.Log, msg));
        });
        CheckRunner.setToolWarningCallback(msg ->
                clientWarnPrefs(msg, "toolOptions"));
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
        ServerLog.serverLog("[didOpen] uri=" + uri);
        lastContent.put(uri, content);
        // Cache the nav-dirty flag for this project so didChange needs no lookup.
        String openPid = projectIdForUri(uri);
        AtomicBoolean d = openPid != null ? projectNavDirty.get(openPid) : null;
        currentNavDirty = (d != null) ? d : NOOP_DIRTY;

        // Notify the client to re-query code lenses now that lastContent is populated.
        // This ensures the initial "—" status appears even before the first --check.
        refreshCodeLenses();

        // --check: on open unless manual-only mode
        if (!globalSettings.isCheckManual()) scheduleCheckNow(uri, content, openPid);
        // ESC is never triggered on open — only on save/edit (per trigger setting)
        // or the explicit openjml.runEsc command.
    }

    @Override
    public void didChange(DidChangeTextDocumentParams params) {
        if (params.getContentChanges().isEmpty()) return;
        String uri     = params.getTextDocument().getUri();
        ServerLog.serverLog("[didChange] uri=" + uri);
        String content = Boolean.TRUE.equals(globalSettings.clientSettings.incrementalSync)
                ? IncrementalSyncApplier.apply(lastContent.get(uri),
                                               params.getContentChanges())
                : params.getContentChanges().get(0).getText();
        lastContent.put(uri, content);
        dirtyUris.add(uri);
        currentNavDirty.set(true);
        // Invalidate cached check state for all other open files so that focus-triggered
        // rechecks pick up this change in their cross-file context.  When the primary
        // check completes, companion files that were actually compiled will be re-marked
        // as up-to-date, so only truly-uncompiled files will be rechecked on focus.
        lastCheckedContent.keySet().removeIf(k -> !k.equals(uri));

        // --check: debounced if in edit mode
        ServerLog.serverLog("[didChange.jml] isCheckOnEdit=" + globalSettings.isCheckOnEdit() + " uri=" + uri);
        if (globalSettings.isCheckOnEdit()) {
            if (uri.endsWith(".jml")) {
                // .jml files are spec files; redirect check to companion .java.
                // The dirty .jml content is already in lastContent so checkWithContext
                // will use it when writing the temp directory.
                String javaUri = resolveCompanionJavaUri(uri, content);
                ServerLog.serverLog("[didChange.jml] resolveCompanionJavaUri=" + javaUri);
                if (javaUri != null) {
                    final String fJavaUri = javaUri;
                    debounce(pendingCheck, fJavaUri,
                            () -> { String jc = lastContent.get(fJavaUri);
                                    ServerLog.serverLog("[didChange.jml] running check on " + fJavaUri + " jc=" + (jc == null ? "null" : "present"));
                                    if (jc != null) runCheckContent(fJavaUri, jc); },
                            CHECK_DEBOUNCE_MS);
                }
            } else {
                debounce(pendingCheck, uri,
                        () -> runCheckContent(uri, content),
                        CHECK_DEBOUNCE_MS);
            }
        }

    }

    @Override
    public void didSave(DidSaveTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        ServerLog.serverLog("[textDocument/didSave] uri=" + uri);
        dirtyUris.remove(uri);
        cancelPending(uri);

        // --check: on save unless manual-only mode.  projectId is unavailable from
        // the LSP didSave message; null causes a root-path lookup in scheduleCheckFile.
        if (!globalSettings.isCheckManual()) scheduleCheckFile(uri, null);

        // --esc: on save when escTriggerOn == "save".  LSP does not carry a save-reason
        // (manual vs. auto-save), so this fires on every didSave regardless of how the
        // save was initiated.
        if (globalSettings.isEscOnSave()) scheduleEscForUri(uri, null);
    }

    @Override
    public void didClose(DidCloseTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        ServerLog.serverLog("[textDocument/didClose] uri=" + uri);
        dirtyUris.remove(uri);    // unsaved changes are gone when the editor closes
        lastContent.remove(uri);  // in-memory editor buffer is gone; reads fall back to disk
        // Retain all pending/running checks, proof results, AST cache, and diagnostics.
        // Closing an editor does not affect project-level analysis state — checks may
        // still be running for this file and results remain valid for the Problems panel.
        // Do NOT publish empty diagnostics.
    }

    // --- code lens ---

    @Override
    public CompletableFuture<List<? extends CodeLens>> codeLens(CodeLensParams params) {
        String uri = params.getTextDocument().getUri();
        ServerLog.serverLog("[textDocument/codeLens] uri=" + uri);
        // .jml spec files: show lenses for model methods declared in this file.
        if (uri.endsWith(".jml")) return codeLensForJml(uri);

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
                ? JavaSourceScanner.findMethodsFromAst(astEntry.ast())
                : List.of();

        List<CodeLens> lenses = new ArrayList<>(methods.size());
        for (JavaSourceScanner.MethodInfo m : methods) {
            if (!m.sourceUri().isEmpty() && !m.sourceUri().equals(uri)) continue;
            ProofResult pr = proofResults.get(methodKey(uri, m));
            MethodStatus s = (pr != null) ? pr.status() : MethodStatus.UNKNOWN;
            // Use the project ID from the last proof result if available; otherwise derive
            // it from the URI so that code lenses created before the first ESC run still
            // carry the correct project ID (Eclipse registers projects by name, not "").
            String proj = (pr != null && pr.projectId() != null && !pr.projectId().isEmpty())
                    ? pr.projectId()
                    : (projectIdForUri(uri) != null ? projectIdForUri(uri) : "");
            var range = new Range(new Position(m.startLine(), 0),
                                  new Position(m.startLine(), 0));
            // Method reference is the unique per-project FQN (rawName from
            // Utils.uniqueSymbolName), e.g. "com.example.MyClass.add(int,int)".
            // This uniquely identifies the method across the project without relying on
            // line numbers, which shift as code is edited.
            String methodRef = m.rawName();
            // While CHECKING, the lens acts as a "skip this proof" button:
            // it sends abortMethodProof(rawName) so only this method is aborted
            // and the ESC loop continues.  Otherwise it sends runEscForMethod.
            boolean checking = s.result() == EscResult.CHECKING;
            String cmd  = checking ? OpenJMLCommands.ABORT_METHOD_PROOF
                                   : OpenJMLCommands.RUN_ESC_FOR_METHOD;
            List<Object> args = List.<Object>of(proj, uri, methodRef);
            lenses.add(new CodeLens(range, new Command(s.label(), cmd, args), null));
        }
        return CompletableFuture.completedFuture(lenses);
    }

    /**
     * Return code lenses for a {@code .jml} spec file.
     *
     * <p>Only shown when the {@code .jml} file is open in an editor
     * ({@link #lastContent} has its content).  Each lens targets the companion
     * {@code .java} file for ESC, because model methods must be verified together
     * with the Java implementation; passing a {@code .jml} file directly to
     * OpenJML is not supported.
     *
     * <p>Clicking a lens triggers whole-file ESC on the companion {@code .java}
     * file.  After the run completes, {@link #updateEscStatus} propagates the
     * proof results back to this {@code .jml} editor's status map so the lenses
     * update.
     */
    private CompletableFuture<List<? extends CodeLens>> codeLensForJml(String jmlUri) {
        String jmlContent = lastContent.get(jmlUri);
        if (jmlContent == null) return CompletableFuture.completedFuture(List.of());

        ASTCache.Entry jmlEntry = CheckRunner.getASTCache().get(jmlUri);
        if (jmlEntry == null) return CompletableFuture.completedFuture(List.of());

        JmlCompilationUnit jmlAst = jmlEntry.ast();
        if (jmlAst.sourceCU == null || jmlAst.sourceCU.sourcefile == null)
            return CompletableFuture.completedFuture(List.of());
        String javaUri = jmlAst.sourceCU.sourcefile.toUri().normalize().toString();

        // Use the .jml CU and .jml content so line numbers are correct for the .jml editor.
        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(jmlAst);

        List<CodeLens> lenses = new ArrayList<>(methods.size());
        for (JavaSourceScanner.MethodInfo m : methods) {
            ProofResult pr = proofResults.get(methodKey(jmlUri, m));
            MethodStatus s = (pr != null) ? pr.status() : MethodStatus.UNKNOWN;
            var range = new Range(new Position(m.startLine(), 0), new Position(m.startLine(), 0));
            // Command targets the .java file — ESC runs on the .java file.
            // An empty method reference triggers whole-file ESC; model methods are proved
            // together with the Java implementation and do not support split-by-method
            // targeting across files.
            String jmlProj = (pr != null && pr.projectId() != null && !pr.projectId().isEmpty())
                    ? pr.projectId()
                    : (projectIdForUri(javaUri) != null ? projectIdForUri(javaUri) : "");
            lenses.add(new CodeLens(range,
                    new Command(s.label(), OpenJMLCommands.RUN_ESC_FOR_METHOD,
                                List.<Object>of(jmlProj, javaUri, "")),
                    null));
        }
        return CompletableFuture.completedFuture(lenses);
    }

    // --- hover ---

    @Override
    public CompletableFuture<Either<List<CompletionItem>, CompletionList>> completion(
            CompletionParams params) {
        String uri     = params.getTextDocument().getUri();
        ServerLog.serverLog("[textDocument/completion] uri=" + uri);
        String content = lastContent.get(uri);
        if (content == null) return CompletableFuture.completedFuture(Either.forLeft(List.of()));
        List<CompletionItem> items =
                JmlCompletionProvider.complete(content, params.getPosition());
        return CompletableFuture.completedFuture(Either.forLeft(items));
    }

    private List<Either<SymbolInformation, DocumentSymbol>> buildSymbolResult(
            ASTCache.Entry entry, String content) {
        boolean jmlOnly = !Boolean.TRUE.equals(globalSettings.clientSettings.useIntegratedOutline);
        List<DocumentSymbol> symbols = DocumentSymbolProvider.fromAst(entry.ast(), content, jmlOnly);
        List<Either<SymbolInformation, DocumentSymbol>> result = new ArrayList<>(symbols.size());
        for (DocumentSymbol ds : symbols) result.add(Either.forRight(ds));
        return result;
    }

    @Override
    public CompletableFuture<List<Either<SymbolInformation, DocumentSymbol>>> documentSymbol(
            DocumentSymbolParams params) {
        String uri     = params.getTextDocument().getUri();
        ServerLog.serverLog("[textDocument/documentSymbol] uri=" + uri);
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
                return buildSymbolResult(e2, finalContent);
            });
        }
        ASTCache.Entry entry = CheckRunner.getASTCache().get(cacheUri);
        if (entry == null) {
            return CompletableFuture.completedFuture(List.of());
        }
        List<Either<SymbolInformation, DocumentSymbol>> result = buildSymbolResult(entry, content);
        return CompletableFuture.completedFuture(result);
    }

    @Override
    public CompletableFuture<List<FoldingRange>> foldingRange(FoldingRangeRequestParams params) {
        String uri     = params.getTextDocument().getUri();
        ServerLog.serverLog("[textDocument/foldingRange] uri=" + uri);
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
        ServerLog.serverLog("[textDocument/hover] uri=" + uri);
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

        // If a diagnostic covers this position, let it take precedence.
        List<Diagnostic> uriDiags = checkDiags.get(uri);
        if (uriDiags != null) {
            for (Diagnostic d : uriDiags) {
                org.eclipse.lsp4j.Range r = d.getRange();
                int sl = r.getStart().getLine(), el = r.getEnd().getLine();
                int sc = r.getStart().getCharacter(), ec = r.getEnd().getCharacter();
                boolean covers = (line > sl || (line == sl && col >= sc))
                              && (line < el || (line == el && col <= ec));
                if (covers) return CompletableFuture.completedFuture(null);
            }
        }

        // Show the JML spec only when hovering over the signature (not the body).
        ASTCache.Entry hoverAstEntry = CheckRunner.getASTCache().get(uri);
        List<JavaSourceScanner.MethodInfo> methods = (hoverAstEntry != null)
                ? JavaSourceScanner.findMethodsFromAst(hoverAstEntry.ast())
                : List.of();
        JavaSourceScanner.MethodInfo method = null;
        for (JavaSourceScanner.MethodInfo m : methods) {
            if (m.onSignature(line)) {
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
        ServerLog.serverLog("[textDocument/signatureHelp] uri=" + uri);
        String content = lastContent.get(uri);
        return CompletableFuture.completedFuture(
                SignatureHelpProvider.compute(params, content, CheckRunner.getASTCache()));
    }

    // --- inlay hints ---

    @Override
    public CompletableFuture<List<InlayHint>> inlayHint(InlayHintParams params) {
        String uri     = params.getTextDocument().getUri();
        ServerLog.serverLog("[textDocument/inlayHint] uri=" + uri);
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
        ServerLog.serverLog("[textDocument/definition] uri=" + uri);
        String source = lastContent.get(uri);
        if (source == null)
            return CompletableFuture.completedFuture(Either.forLeft(List.of()));

        return ensureNavCacheReady().thenCompose(v -> {
            ASTCache cache = CheckRunner.getASTCache();
            boolean hasAst = cache.get(uri) != null;
            ServerLog.serverLog("[OpenJML] definition: uri=" + uri
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
                            ServerLog.serverLog("[FindDeclaration] definition: no AST for " + javaUri);
                            return Either.<List<? extends Location>, List<? extends LocationLink>>
                                    forLeft(List.of());
                        }
                        ServerLog.serverLog("[FindDeclaration] definition: redirecting to java AST " + javaUri);
                        Map<String, String> synthetic = new java.util.HashMap<>(lastContent);
                        synthetic.put(javaUri, jmlSource);
                        Location loc = DefinitionFinder.findDefinition(
                                javaUri,
                                params.getPosition().getLine(),
                                params.getPosition().getCharacter(),
                                synthetic,
                                cache);
                        ServerLog.serverLog("[FindDeclaration] definition result (jml): " + DefinitionFinder.locStr(loc));
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

            ServerLog.serverLog("[OpenJML] definition result: " + DefinitionFinder.locStr(loc));
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
        ServerLog.serverLog("[textDocument/references] uri=" + uri);
        if (lastContent.get(uri) == null)
            return CompletableFuture.completedFuture(List.of());

        boolean includeDecl = params.getContext() != null
                && params.getContext().isIncludeDeclaration();

        return ensureFreshAndConfirm(uri, "Find References").thenApply(proceed -> {
            if (!proceed) return List.of();
            String refPid = projectIdForUri(uri);
            if (refPid != null) waitForProjectNav(refPid).join();
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
        ServerLog.serverLog("[textDocument/documentHighlight] uri=" + uri);
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
        ServerLog.serverLog("[textDocument/declaration] uri=" + uri);
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
        ServerLog.serverLog("[textDocument/prepareRename] uri=" + uri);
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
        ServerLog.serverLog("[textDocument/rename] uri=" + uri);
        if (lastContent.get(uri) == null)
            return CompletableFuture.completedFuture(null);

        return ensureFreshAndConfirm(uri, "Rename").thenCompose(proceed -> {
            if (!proceed) return CompletableFuture.completedFuture(null);
            try {
                String renamePid = projectIdForUri(uri);
                if (renamePid != null) waitForProjectNav(renamePid).join();
                OpenJMLSettings renameS = settingsForUri(uri);
                if (renameS == null) return null;
                Renamer.RenameResponse resp = Renamer.renameWithErrors(
                        uri,
                        params.getPosition().getLine(),
                        params.getPosition().getCharacter(),
                        params.getNewName(),
                        lastContent,
                        CheckRunner.getASTCache(),
                        renameS,
                        checkDiags);
                if (resp.hasErrors()) {
                    String allMsgs = String.join("\n", resp.errors());
                    throw new ResponseErrorException(new org.eclipse.lsp4j.jsonrpc.messages.ResponseError(
                            org.eclipse.lsp4j.jsonrpc.messages.ResponseErrorCode.InvalidParams,
                            "Rename would introduce errors:\n" + allMsgs,
                            resp.edit()));
                }
                WorkspaceEdit edit = resp.edit();
                // Proactively update lastContent for open files modified by the rename.
                // Eclipse (and some other clients) do not send textDocument/didChange
                // after applying a server-initiated WorkspaceEdit, so the server must
                // update its own snapshot to avoid serving stale content on the next check.
                if (edit != null && edit.getChanges() != null) {
                    edit.getChanges().forEach((fileUri, edits) -> {
                        boolean inLastContent = lastContent.containsKey(fileUri);
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

        // (dirty snapshot is taken inside the debounce callback — see below)

        // Cancel any per-URI debounce checks that are pending for these specific
        // files.  This is important for post-rename coordination: the client sends
        // this command after applying all edits, so the individual per-URI debounces
        // triggered by each didChange are superseded by this combined check.
        for (String path : pathsCopy) {
            try {
                String uri = java.nio.file.Path.of(path).toUri().normalize().toString();
                cancelPending(uri);
            } catch (Exception ignored) {}
        }

        // Debounce: cancel any previously scheduled check-paths task so that rapid
        // toolbar clicks collapse into a single check.  A 300 ms delay is short enough
        // to feel immediate but long enough to absorb a double-click burst.
        ScheduledFuture<?> prev = pendingCheckPaths;
        if (prev != null) prev.cancel(false);
        pendingCheckPaths = scheduler.schedule(() -> {
            pendingCheckPaths = null;
            // Snapshot dirty content here (inside the debounce callback) so that
            // all didChange notifications from the rename have been processed before
            // the snapshot is taken.
            Map<String, String> snapshot = dirtySnapshot();
            executor.submit(() -> {
                try {
                    CheckRunner.DirCheckResult result = CheckRunner.runCheckDirWithContext(pathsCopy, snapshot, s, projectId);
                    if (result.exitCode() == 2) {
                        reportCommandLineError(result.diagnosticsByUri().values().stream()
                                .flatMap(List::stream).collect(java.util.stream.Collectors.toList()));
                        return;
                    }
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
                    ServerLog.serverLog("[scheduleCheckForPaths] error: " + e.getMessage());
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
    /**
     * Triggers an ESC run on a list of OS paths (files or directories), grouped
     * under one session key.  Called from the {@code openjml.runEsc} command and
     * from {@link #scheduleEscFile} for single-file auto-ESC.
     */
    private void scheduleEscForPaths(List<String> paths, OpenJMLSettings s, String projectId) {
        if (paths == null || paths.isEmpty()) return;

        // Pre-mark open single files as UNKNOWN before submitting so lenses
        // immediately show idle state.  Directory paths are handled after the run.
        for (String path : paths) {
            try {
                java.nio.file.Path p = java.nio.file.Path.of(path);
                if (!java.nio.file.Files.isDirectory(p)) {
                    String uri = p.toUri().toString();
                    if (lastContent.containsKey(uri)) {
                        long pendingGen = sessionCounter.get() + 1;
                        markAllMethodStatus(uri, MethodStatus.UNKNOWN, pendingGen, projectId);
                    }
                }
            } catch (Exception ignored) {}
        }
        refreshCodeLenses();

        // Build ESC snapshot: dirty files + any in-memory-only files in paths that have no
        // disk counterpart (e.g. virtual test URIs or files never saved).
        Map<String, String> escSnapshot;
        {
            Map<String, String> snap = new java.util.HashMap<>(dirtySnapshot());
            for (String path : paths) {
                try {
                    java.nio.file.Path pp = java.nio.file.Path.of(path);
                    if (!java.nio.file.Files.isDirectory(pp) && !java.nio.file.Files.exists(pp)) {
                        String uri = pp.toUri().toString();
                        String content = lastContent.get(uri);
                        if (content != null) snap.putIfAbsent(uri, content);
                    }
                } catch (Exception ignored) {}
            }
            escSnapshot = java.util.Collections.unmodifiableMap(snap);
        }
        String batchKey = paths.get(0);
        java.util.Set<String> batchUriKeys =
                java.util.Collections.newSetFromMap(new java.util.concurrent.ConcurrentHashMap<>());

        submitEscJob(batchKey, s.escPool, projectId, (myBatchGen, hook, futureRef) -> {
            // Wrap hook so the batch IAPI is accessible from the RUNNING callback.
            var batchApiRef = new java.util.concurrent.atomic.AtomicReference<IAPI>();
            java.util.function.Consumer<IAPI> batchHook =
                    api -> { hook.accept(api); batchApiRef.set(api); };
            try {
                CheckRunner.DirCheckResult result = CheckRunner.runEscDirWithContext(
                        paths, escSnapshot, s, (uri, methodName, diags, partialResults, partialDiagsByMethod) -> {
                    if (client == null) return;
                    if (!isCurrentSession(batchKey, myBatchGen)) return;
                    if (diags == null) {
                        // RUNNING event: method proof just started.
                        IAPI batchApi = batchApiRef.get();
                        if (batchApi != null) {
                            runningSessions.put(uri, new RunningSession(myBatchGen,
                                    futureRef.get(),
                                    new java.util.concurrent.atomic.AtomicReference<>(batchApi),
                                    false /* batch sub-entry — not shown in Cancel ESC list */,
                                    projectId));
                            batchUriKeys.add(uri);
                        }
                        markMethodCheckingByName(uri, methodName, myBatchGen, projectId);
                        publishMerged(uri);
                        executor.execute(OpenJMLTextDocumentService.this::refreshCodeLenses);
                    } else {
                        // COMPLETION event: update status progressively.
                        ServerLog.serverLog("[scheduleEscForPaths] COMPLETION uri=" + uri
                                + " method=" + methodName
                                + " partialResults=" + partialResults.size());
                        updateEscStatusPartial(uri, partialResults, myBatchGen, partialDiagsByMethod, projectId);
                        publishMerged(uri);
                        refreshCodeLenses();
                    }
                }, batchHook);
                if (client == null) return;
                if (result.exitCode() == 2) {
                    reportCommandLineError(result.diagnosticsByUri().values().stream()
                            .flatMap(List::stream).collect(java.util.stream.Collectors.toList()));
                    return;
                }
                // Update code-lens status and publish diagnostics for ALL files in the run,
                // whether or not they are currently open in an editor.
                // collectJavaFiles covers real on-disk files; the second loop adds in-memory
                // files (e.g. content-only URIs in lastContent) that don't exist on disk.
                java.util.Set<String> urisToUpdate = new java.util.LinkedHashSet<>();
                for (java.nio.file.Path javaFile : collectJavaFiles(paths)) {
                    urisToUpdate.add(javaFile.toUri().toString());
                }
                for (String p : paths) {
                    try {
                        java.nio.file.Path pp = java.nio.file.Path.of(p);
                        if (!java.nio.file.Files.isDirectory(pp)) {
                            String uri = pp.toUri().toString();
                            if (lastContent.containsKey(uri)) urisToUpdate.add(uri);
                        }
                    } catch (Exception ignored) {}
                }
                for (String uri : urisToUpdate) {
                    updateEscStatus(uri,
                            result.proofResults(), result.exitCode(), List.of(), myBatchGen,
                            result.diagsByMethod(), projectId);
                    publishMerged(uri);
                }
            } catch (Throwable e) {
                ServerLog.serverLog("[scheduleEscForPaths] error: " + e.getMessage());
            } finally {
                batchUriKeys.forEach(runningSessions::remove);
            }
        });
    }

    void scheduleEscForPaths(List<String> paths, String projectId) {
        scheduleEscForPaths(paths, settingsForProject(projectId), projectId);
    }

    /**
     * Recursively walk {@code paths} (OS files or directories) collecting all
     * {@code .java} files, deduplicating by path.
     */
    private static List<java.nio.file.Path> collectJavaFiles(List<String> paths) {
        List<java.nio.file.Path> result = new java.util.ArrayList<>();
        java.util.Set<String> seenRealPaths = new java.util.LinkedHashSet<>();
        for (String p : paths) {
            java.nio.file.Path root = java.nio.file.Path.of(p);
            if (!java.nio.file.Files.exists(root)) continue;
            try (var stream = java.nio.file.Files.walk(root,
                    java.nio.file.FileVisitOption.FOLLOW_LINKS)) {
                stream.filter(f -> java.nio.file.Files.isRegularFile(f)
                                && f.toString().endsWith(".java"))
                      .forEach(f -> {
                          String realPath;
                          try { realPath = f.toRealPath().toString(); }
                          catch (java.io.IOException e) { realPath = f.normalize().toAbsolutePath().toString(); }
                          if (seenRealPaths.add(realPath)) result.add(f);
                      });
            } catch (java.io.IOException | java.io.UncheckedIOException e) {
                ServerLog.serverLog("[collectJavaFiles] error walking " + p + ": " + e);
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
        ServerLog.serverLog("[scheduleEscSplitByFile] paths received: " + paths);
        OpenJMLSettings s = settingsForProject(projectId);
        List<java.nio.file.Path> javaFiles = collectJavaFiles(paths);
        ServerLog.serverLog("[scheduleEscSplitByFile] java files found: " + javaFiles);
        // Expand paths to individual .java files and queue each as its own ESC job.
        // scheduleEscForPaths immediately submits to escPool via submitEscJob, so all
        // files are queued before any begin running, and each gets incremental updates.
        for (java.nio.file.Path javaFile : javaFiles) {
            scheduleEscForPaths(List.of(javaFile.toString()), s, projectId);
        }
    }

    /**
     * Split-by-method ESC: recursively expand {@code paths} to individual {@code .java}
     * files, discover methods in each via the AST cache, and submit each method as a
     * separate ESC task on {@link OpenJMLSettings#escPool}.
     *
     * <p>If the AST cache has no entry for a file (e.g. it has never been opened via
     * {@code didOpen}), a {@code --check} run is performed first to populate it.
     * File content is read synchronously before task submission so that method
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
                    ServerLog.serverLog("[scheduleEscSplitByMethod] cannot read " + javaFile + ": " + e);
                    continue;
                }
            }
            final String finalContent = content;

            ASTCache.Entry astEntry = CheckRunner.getASTCache().get(uri);
            if (astEntry == null) {
                // No AST yet (file not opened via didOpen) — run --check to discover methods.
                // runCheckDir stores entries in the nav tier; use getNav() to retrieve them.
                CheckRunner.runCheckDirWithContext(List.of(javaFile.toString()), snapshot, s);
                astEntry = CheckRunner.getASTCache().getNav(uri);
            }
            List<JavaSourceScanner.MethodInfo> methods = (astEntry != null)
                    ? JavaSourceScanner.findMethodsFromAst(astEntry.ast())
                    : List.of();
            if (methods.isEmpty()) continue;

            for (JavaSourceScanner.MethodInfo method : methods) {
                final String methodName = method.name();
                submitEscForMethod(uri, method,
                        hook -> CheckRunner.escMethodWithContext(
                                uri, finalContent, methodName, snapshot, s, hook),
                        s.escPool, projectId);
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
     * stored in {@code checkDiags} and published via {@link #publishMerged} for
     * each affected URI.
     */
    void scheduleRacForPaths(List<String> paths, String projectId, String outputDir) {
        if (paths == null || paths.isEmpty()) return;
        OpenJMLSettings base = settingsForProject(projectId);
        // In the Eclipse format, racOutputDir is null (already in base.racOutputDir via ProjectConfig).
        // When racOutputDir is passed explicitly (e.g. legacy commands), it must override.
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
                    storeCheckDiags(uri, diags);
                    publishMerged(uri);
                });
                // Clear stale diags for paths not in the result.
                for (String path : pathsCopy) {
                    String uri;
                    try { uri = java.nio.file.Path.of(path).toUri().toString(); }
                    catch (Exception e) { continue; }
                    if (!result.allDiagnostics().containsKey(uri)) {
                        storeCheckDiags(uri, List.of());
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
                ServerLog.serverLog("[scheduleRacForPaths] error: " + e.getMessage());
                clientError("RAC failed: " + e.getMessage());
            }
        });
    }

    /**
     * Return the flat semantic token integer data for {@code uri}, or an empty
     * list if the file is not currently open.  Called by the workspace service
     * in response to the {@code openjml.getSemanticTokens} command so the VS
     * Code extension can register a direct {@code DocumentSemanticTokensProvider}
     * that merges additively with the Red Hat Java extension's tokens.
     */
    List<Integer> getSemanticTokens(String uri) {
        String content = lastContent.get(uri);
        if (content == null) {
            ServerLog.serverLog("[getSemanticTokens] no content for uri=" + uri);
            return List.of();
        }
        // "regex" strategy: always use regex (instant, works before first --check).
        // "ast" strategy (default): prefer AST-based when an attributed AST is
        // available (no false positives), fall back to regex before first --check.
        if (!globalSettings.isRegexColoring()) {
            ASTCache cache = CheckRunner.getASTCache();
            // For .jml files: try the direct .jml AST entry first; if absent, try the
            // companion .java AST (whose walker emits tokens with positions relative to
            // the .jml source file when it visits JML spec nodes in that file).
            ASTCache.Entry entry = cache.get(uri);
            if (entry == null) entry = cache.getNav(uri);
            if (entry == null && uri.endsWith(".jml")) {
                String javaUri = resolveCompanionJavaUri(uri, content);
                if (javaUri != null) {
                    entry = cache.get(javaUri);
                    if (entry == null) entry = cache.getNav(javaUri);
                }
            }
            ServerLog.serverLog("[getSemanticTokens] uri=" + uri
                    + " astEntry=" + (entry != null ? "present" : "absent")
                    + " specsCompilationUnit=" + (entry != null && entry.ast().specsCompilationUnit != null
                        ? (entry.ast().specsCompilationUnit == entry.ast() ? "self" : "other") : "null"));
            if (entry != null) {
                try {
                    // Guard: if the cached AST was built from a different version of the
                    // file, its character offsets may exceed the current content length,
                    // causing StringIndexOutOfBoundsException.  Fall through to regex.
                    // For .jml files we may be using the companion .java AST; in that case
                    // compare against the .jml source recorded on the AST's specsCompilationUnit
                    // if present, or skip the length check (the walker guards on pos bounds).
                    boolean stale = false;
                    try {
                        CharSequence astSrc = entry.ast().sourcefile.getCharContent(false);
                        // If this is a .java AST used for a .jml file, the lengths differ by design.
                        if (!uri.endsWith(".jml")) stale = (astSrc.length() != content.length());
                    } catch (Exception ignored) {}
                    if (!stale) {
                        boolean fullMode = globalSettings.isOverwriteJavaColoring();
                        List<Integer> data = SemanticTokensProvider.computeTokensFromAst(entry, content, fullMode).getData();
                        ServerLog.serverLog("[getSemanticTokens] AST path: fullMode=" + fullMode
                                + " tokens=" + data.size() / 5 + " ints=" + data.size());
                        return data;
                    } else {
                        ServerLog.serverLog("[getSemanticTokens] AST stale — falling back to regex");
                    }
                } catch (Exception e) {
                    ServerLog.serverLog("[getSemanticTokens] AST walk threw: " + e + " — falling back to regex");
                }
            }
        }
        List<Integer> data = SemanticTokensProvider.computeTokens(content).getData();
        ServerLog.serverLog("[getSemanticTokens] regex path: tokens=" + data.size() / 5
                + " ints=" + data.size());
        return data;
    }

    /**
     * Handle {@code textDocument/semanticTokens/full} requests from LSP clients
     * (e.g. Eclipse via LSP4E's {@code SemanticHighlightReconcilerStrategy}).
     */
    @Override
    public CompletableFuture<org.eclipse.lsp4j.SemanticTokens> semanticTokensFull(
            org.eclipse.lsp4j.SemanticTokensParams params) {
        ServerLog.serverLog("[textDocument/semanticTokens/full]");
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
    List<org.eclipse.lsp4j.WorkspaceSymbol> symbols(String query) {
        return symbols(query, null);
    }

    /**
     * Query the declaration index restricted to a named project.
     * Resolves the project ID to its configured root paths and delegates to
     * {@link #symbols(String, String)}.  An unknown ID is reported as an error
     * and returns an empty list.  A null/empty ID searches all projects.
     */
    List<org.eclipse.lsp4j.WorkspaceSymbol> symbolsForProject(String query, String projectId) {
        if (projectId != null && !projectId.isEmpty() && !isKnownProject(projectId)) {
            clientError("OpenJML: symbolsForProject — unknown project id '" + projectId + "'.");
            return List.of();
        }
        // Ensure nav cache is up to date before querying.
        waitForProjectNav(projectId != null && !projectId.isEmpty() ? projectId : null).join();
        ASTCache cache = CheckRunner.getASTCache();
        ServerLog.serverLog("[symbolsForProject] navSectionKeys=" + cache.navSectionKeys()
                + " liveDecls=" + cache.liveDeclarationCount()
                + " query=\"" + (query != null ? query : "")
                + "\" project=" + (projectId != null && !projectId.isEmpty() ? projectId : "(all)"));
        List<org.eclipse.lsp4j.WorkspaceSymbol> result = collectSymbols(query,
                cb -> cache.forEachDeclarationForProject(projectId, cb));
        ServerLog.serverLog("[symbolsForProject] -> " + result.size() + " result(s)"
                + (result.isEmpty() ? "" : ", first=" + result.get(0).getName()));
        return result;
    }

    /** Build a {@code WorkspaceSymbol} list by iterating declarations via {@code iterator}. */
    private List<org.eclipse.lsp4j.WorkspaceSymbol> collectSymbols(String query,
            java.util.function.Consumer<java.util.function.BiConsumer<
                    com.sun.tools.javac.code.Symbol, ASTCache.SymbolLocation>> iterator) {
        final String effectiveQuery = (query == null ? "" : query.trim());
        List<org.eclipse.lsp4j.WorkspaceSymbol> result = new ArrayList<>();
        iterator.accept((sym, loc) -> {
            String name = sym.name.toString();
            if (name.isEmpty() || name.startsWith("<")) return;
            if (!effectiveQuery.isEmpty()
                    && !name.toLowerCase().contains(effectiveQuery.toLowerCase())) return;
            String content = lastContent.get(loc.uri());
            if (content == null) {
                String path = CheckRunner.uriToPath(loc.uri());
                if (path != null) {
                    try { content = java.nio.file.Files.readString(java.nio.file.Path.of(path)); }
                    catch (java.io.IOException e) {
                        ServerLog.serverLog("[OpenJML] symbols: cannot read " + loc.uri()
                                + ": " + e.getMessage());
                    }
                }
            }
            if (content == null) return;
            Position start = offsetToPosition(content, loc.charOffset());
            Position end   = offsetToPosition(content, loc.charOffset() + name.length());
            var location = new Location(loc.uri(), new Range(start, end));
            var ws = new org.eclipse.lsp4j.WorkspaceSymbol(name, symbolKind(sym),
                    Either.forLeft(location));
            result.add(ws);
        });
        return result;
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
     * @param query       identifier substring to match (case-insensitive), optionally
     *                    prefixed with a project root and newline; empty = return all
     * @param projectRoot explicit project-root filter; takes precedence over any
     *                    root encoded in {@code query}; {@code null} = no filter
     */
    List<org.eclipse.lsp4j.WorkspaceSymbol> symbols(String query, String projectRoot) {
        // Extract the encoded project ID before trimming: trim() strips trailing '\n',
        // which would hide an empty identifier after "ProjectId\n".
        String projectId = projectRoot; // explicit argument takes precedence
        String raw;
        int nlIdx = (query != null) ? query.indexOf('\n') : -1;
        if (nlIdx >= 0 && projectId == null) {
            projectId = query.substring(0, nlIdx).trim();
            raw = query.substring(nlIdx + 1).trim();
            if (projectId.isEmpty()) projectId = null;
        } else {
            raw = query == null ? "" : query.trim();
        }

        // Strip any surrounding quote characters that a client might accidentally include.
        if (raw.length() >= 2
                && ((raw.startsWith("\"") && raw.endsWith("\""))
                    || (raw.startsWith("'") && raw.endsWith("'")))) {
            raw = raw.substring(1, raw.length() - 1).trim();
        }
        ServerLog.serverLog("[symbols] query=\"" + raw + "\""
                + (projectId != null ? " projectId=\"" + projectId + "\"" : ""));

        // When a project ID is present, delegate to symbolsForProject which
        // searches only that project's ASTs and waits for nav to be ready.
        if (projectId != null && !projectId.isEmpty()) {
            return symbolsForProject(raw, projectId);
        }

        List<org.eclipse.lsp4j.WorkspaceSymbol> result =
                collectSymbols(raw, cb -> CheckRunner.getASTCache().forEachDeclaration(null, cb));
        ServerLog.serverLog("[symbols] returning " + result.size() + " result(s)"
                + (result.isEmpty() ? "" : ", first URI=" + result.get(0).getLocation().getLeft().getUri()));
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
     * racOutputDir/javaOutputDir) override the global settings when non-null; all other
     * fields are inherited.  {@code toolOptions} is global-only and is inherited unchanged.
     * The {@code "__workspace__"} project has no overrides and therefore inherits everything
     * from global settings.
     */
    public void updateProjectSettings(List<ProjectConfig> configs) {
        projectSettings.clear();
        if (configs == null) return;
        for (ProjectConfig cfg : configs) {
            if (cfg.id == null) continue;
            OpenJMLSettings s = new OpenJMLSettings(globalSettings);
            s.projectId  = cfg.id;
            s.sourcePath = OpenJMLSettings.expandEnvVarsInPath(cfg.sourcePath != null ? cfg.sourcePath : "");
            s.classPath  = OpenJMLSettings.expandEnvVarsInPath(cfg.classPath  != null ? cfg.classPath  : "");
            s.javaOutputDir = cfg.javaOutputDir != null ? cfg.javaOutputDir : "";
            // Compute effective racOutputDir with javaOutputDir as fallback.
            String rawRac = cfg.racOutputDir != null ? cfg.racOutputDir
                    : (globalSettings.racOutputDir != null ? globalSettings.racOutputDir : "");
            s.racOutputDir = rawRac.isBlank() ? s.javaOutputDir : rawRac;
            // specsPath: if non-empty, append sourcePath so OpenJML can find cross-file refs.
            String rawSpecs = cfg.specsPath != null ? cfg.specsPath : globalSettings.specsPath;
            String expandedSpecs = OpenJMLSettings.expandEnvVarsInPath(rawSpecs);
            if (expandedSpecs != null && !expandedSpecs.isBlank()) {
                s.specsPath = expandedSpecs + java.io.File.pathSeparator + s.sourcePath;
            } else {
                s.specsPath = null;
            }
            // Store rootPaths so settingsForUri can match file URIs to this project.
            if (cfg.rootPaths != null && !cfg.rootPaths.isEmpty())
                s.rootPaths = cfg.rootPaths;
            projectSettings.put(cfg.id, s);
        }
        globalSettings.logConfiguration(projectSettings);
    }

    /** Returns {@code true} if {@code projectId} is in the current project registry. */
    boolean isKnownProject(String projectId) {
        return projectSettings.containsKey(projectId);
    }

    /** Returns the stored settings for {@code projectId}, or {@code null} if not found. */
    public OpenJMLSettings getProjectSettings(String projectId) {
        return projectSettings.get(projectId);
    }


    /**
     * Returns the settings for the given project ID, or global settings if the ID is
     * null.  Logs an error if the ID is non-null but not found in the registry
     * (indicates the client submitted an unrecognized project name).
     */
    OpenJMLSettings settingsForProject(String projectId) {
        if (projectId == null) return globalSettings;
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
            if (s.rootPaths == null || s.rootPaths.isEmpty()) {
                wildcard = s;   // catch-all: matches anything not claimed by a specific project
                continue;
            }
            for (String root : s.rootPaths) {
                if (root == null || root.isBlank()) continue;
                String r = root.endsWith(sep) ? root : root + sep;
                if (filePath.startsWith(r)) return s;
            }
        }
        return wildcard;   // null if no wildcard project is registered
    }

    /** Returns the project ID whose rootPaths cover {@code uri}, or null if none match. */
    String projectIdForUri(String uri) {
        String filePath;
        try { filePath = java.net.URI.create(uri).getPath(); }
        catch (Exception e) { return null; }
        String sep = java.io.File.separator;
        for (Map.Entry<String, OpenJMLSettings> e : projectSettings.entrySet()) {
            OpenJMLSettings s = e.getValue();
            if (s.rootPaths == null || s.rootPaths.isEmpty()) continue;
            for (String root : s.rootPaths) {
                if (root == null || root.isBlank()) continue;
                String r = root.endsWith(sep) ? root : root + sep;
                if (filePath.startsWith(r)) return e.getKey();
            }
        }
        return null;
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
        if (uri.endsWith(".jml")) {
            String javaUri = resolveCompanionJavaUri(uri, null);
            ServerLog.serverLog("[scheduleCheckForUri] .jml redirect: javaUri=" + javaUri);
            if (javaUri == null) return;
            final String fJavaUri = javaUri;
            final String javaContent = lastContent.get(javaUri);
            executor.submit(() -> runCheckContent(fJavaUri, javaContent, s));
            return;
        }
        final String content = lastContent.get(uri);
        executor.submit(() -> runCheckContent(uri, content, s));
    }

    /**
     * Trigger a --check recheck of an already-open file (e.g. when focus returns
     * to it after its dependencies were edited).  Uses in-memory content so that
     * unsaved edits are included.  No-op if the file is not currently open.
     */
    void recheckUri(String uri, String projectId) {
        OpenJMLSettings s = projectId != null ? settingsForProject(projectId) : settingsForUri(uri);
        if (s == null) return;
        String content = lastContent.get(uri);
        if (content == null) return;
        // Skip if nothing has changed since the last completed check.
        if (content.equals(lastCheckedContent.get(uri))) return;
        // Skip if a check is already queued or running for this URI (e.g. didOpen
        // schedules a check, then onDidChangeActiveTextEditor fires 200ms later).
        CompletableFuture<Void> pending = lastCheckFuture.get(uri);
        if (pending != null && !pending.isDone()) return;
        final OpenJMLSettings fS = s;
        executor.submit(() -> runCheckContent(uri, content, fS));
    }

    /**
     * Trigger an ESC run on the given URI, dispatching to the engine configured in
     * {@link OpenJMLSettings}: api-mode or fresh.
     */
    void scheduleEscForUri(String uri, String projectId) {
        OpenJMLSettings s = projectId != null ? settingsForProject(projectId) : settingsForUri(uri);
        if (s.isEscApiMode()) {
            submitEscApiWorkList(uri, s, projectId);
        } else {
            scheduleEscFile(uri, s, projectId);
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
    private void submitEscApiWorkList(String uri, OpenJMLSettings s, String projectId) {
        RunningSession prev = runningSessions.remove(uri);
        if (prev != null) prev.future().cancel(false);

        long myGen = sessionCounter.incrementAndGet();
        markEscChecking(uri, myGen, projectId);

        CompletableFuture<CheckRunner.CheckResult> cf =
                CheckRunner.runDoEscFileAsync(uri, s, onMethodEscResult(uri, myGen, projectId));
        attachEscCallbacks(uri, myGen, cf, "api", projectId);
    }

    /**
     * Returns a per-method completion callback shared by both ESC submit methods.
     * Called on a pool thread as each method finishes; updates the code-lens status
     * immediately so the user sees progress.
     */
    private Consumer<CheckRunner.MethodEscResult> onMethodEscResult(String uri, long myGen,
                                                                     String projectId) {
        return methodResult -> {
            if (!isCurrentSession(uri, myGen)) return;
            updateSingleMethodEscStatus(uri, methodResult, myGen, projectId);
            refreshCodeLenses();
        };
    }

    /**
     * Attaches the shared {@code thenAccept}/{@code exceptionally}/{@code whenComplete}
     * completion callbacks to an ESC future and registers it in {@link #runningSessions}.
     *
     * @param modeName short label used in log messages, e.g. {@code "api"} or {@code "fresh"}
     */
    private void attachEscCallbacks(String uri, long myGen,
            CompletableFuture<CheckRunner.CheckResult> cf, String modeName, String projectId) {
        cf.thenAccept(result -> {
            if (!isCurrentSession(uri, myGen)) return;
            List<Diagnostic> primaryDiags =
                    result.allDiagnostics().getOrDefault(uri, result.diagnostics());
            if (result.isInternalError()) {
                ServerLog.serverLog("[OpenJML] ESC (" + modeName + ") internal error (exit code "
                        + result.exitCode() + ")");
                markAllMethodStatus(uri, MethodStatus.CHECK_ERROR, myGen, projectId);
                refreshCodeLenses();
            } else {
                updateEscStatus(uri, result.proofResults(),
                        result.exitCode(), result.foreignMessages(), myGen,
                        result.diagsByMethod(), projectId);
                // diagsByMethod keys are method FQNs; URIs are the inner map keys.
                result.diagsByMethod().values().stream()
                        .flatMap(m -> m.keySet().stream())
                        .filter(u -> !u.equals(uri))
                        .distinct()
                        .forEach(OpenJMLTextDocumentService.this::publishMerged);
                publishMerged(uri);
            }
        }).exceptionally(t -> {
            ServerLog.serverLog("[OpenJML] ESC (" + modeName + ") failed: " + t);
            if (isCurrentSession(uri, myGen)) {
                updateEscStatus(uri, Map.of(), -1, List.of(), myGen, Map.of(), projectId);
                refreshCodeLenses();
            }
            return null;
        }).whenComplete((v, t) -> runningSessions.remove(uri));

        runningSessions.put(uri, new RunningSession(myGen, cf,
                new java.util.concurrent.atomic.AtomicReference<>(), true, projectId));
    }

    /**
     * Update the code-lens status for a single method that completed doESC.
     * Diagnostics for that method are applied; other methods' statuses are
     * unchanged and will be overwritten by the final {@link #updateEscStatus} call.
     */
    private void updateSingleMethodEscStatus(String uri,
                                              CheckRunner.MethodEscResult r, long myGen,
                                              String projectId) {
        // content may be null when file not open in editor; findMethodsFromAst tolerates null.
        String content = lastContent.get(uri);
        ASTCache.Entry escAstEntry = CheckRunner.getASTCache().get(uri);
        List<JavaSourceScanner.MethodInfo> methods = (escAstEntry != null)
                ? JavaSourceScanner.findMethodsFromAst(escAstEntry.ast())
                : List.of();
        for (JavaSourceScanner.MethodInfo m : methods) {
            if (!m.name().equals(r.name())) continue;
            storeProofResult(methodKey(uri, m), myGen,
                    proofResultToStatus(r.kind(), r.diags().size(), r.exitCode(), false),
                    projectId);
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

        // "@line" resolution requires a cached AST.  If the cache is not yet populated
        // (e.g. the file was just opened and the initial check has not finished), run a
        // quick --check now to build the AST, then retry the resolution.
        if (target == null && methodName != null && methodName.startsWith("@") && content != null) {
            CheckRunner.check(uri, content, s);
            target = findMethod(uri, content, methodName);
        }
        // If resolution still failed, refuse to pass "@N" as a raw --method name to OpenJML.
        if (target == null && methodName != null && methodName.startsWith("@")) {
            int displayLine = -1;
            try { displayLine = Integer.parseInt(methodName.substring(1)) + 1; }
            catch (NumberFormatException ignored) {}
            String lineInfo = displayLine >= 0 ? " at line " + displayLine : "";
            String fileName = uri.contains("/") ? uri.substring(uri.lastIndexOf('/') + 1) : uri;
            sendActionMessage(2,
                    "OpenJML: no method found" + lineInfo + " in " + fileName + " — place the cursor inside a method body.",
                    List.of(dismiss()));
            return;
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
                    s.escPool, projectId);
        } else {
            String contentForMethod = lastContent.get(uri);
            Map<String, String> snapshot = dirtySnapshot();
            if (contentForMethod != null) {
                final String c = contentForMethod;
                submitEscForMethod(uri, target,
                        hook -> CheckRunner.escMethodWithContext(uri, c, escMethodName, snapshot, s, hook),
                        s.escPool, projectId);
            } else {
                String filePath = CheckRunner.uriToPath(uri);
                if (filePath != null)
                    submitEscForMethod(uri, target,
                            hook -> CheckRunner.runEscFileMethod(filePath, uri, escMethodName, s, hook),
                            s.escPool, projectId);
            }
        }
    }

    /**
     * Locate a method in {@code content} from a name reference that is either:
     * <ul>
     *   <li>a FQN — e.g. {@code "com.example.MyClass.add(int,int)"} from
     *       {@code Utils.uniqueSymbolName}; exact {@code rawName} match, or</li>
     *   <li>a plain name — simple name match, first occurrence wins.</li>
     * </ul>
     *
     * <p>Uses AST-based method discovery when a cached AST is available for
     * {@code uri}, so that {@link JavaSourceScanner.MethodInfo#rawName()} carries
     * the FQN+signature key needed to look up proof results.  Returns {@code null}
     * if no AST is available (e.g. before the first check completes).
     */
    private static JavaSourceScanner.MethodInfo findMethod(String uri, String content,
                                                            String nameOrRef) {
        if (content == null || nameOrRef == null || nameOrRef.isEmpty()) return null;
        ASTCache.Entry astEntry = uri != null ? CheckRunner.getASTCache().get(uri) : null;
        List<JavaSourceScanner.MethodInfo> methods = (astEntry != null)
                ? JavaSourceScanner.findMethodsFromAst(astEntry.ast())
                : List.of();
        // "@line" format: client passes 0-based cursor line; walk the AST directly to find
        // the innermost method (smallest span) whose declaration contains that line.
        if (nameOrRef.startsWith("@")) {
            if (astEntry == null) return null;
            try {
                int line = Integer.parseInt(nameOrRef.substring(1));
                MethodAtLineScanner scanner = new MethodAtLineScanner(astEntry.ast(), line);
                scanner.scanForMethod(astEntry.ast());
                return scanner.best;
            } catch (NumberFormatException ignored) {}
            return null;
        }
        // Primary: exact FQN match against rawName (e.g. "pkg.Class.method(int,int)").
        for (JavaSourceScanner.MethodInfo m : methods) {
            if (nameOrRef.equals(m.rawName())) return m;
        }
        // Fallback: strip to simple name (drop package/class prefix and parameter types).
        int dot  = nameOrRef.lastIndexOf('.');
        String afterDot  = dot >= 0 ? nameOrRef.substring(dot + 1) : nameOrRef;
        int paren = afterDot.indexOf('(');
        String simpleName = paren >= 0 ? afterDot.substring(0, paren) : afterDot;
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
            ExecutorService pool, String projectId) {
        final String scopeKey = target != null ? methodKey(uri, target) : uri;
        if (target != null) refreshCodeLenses();

        submitEscJob(scopeKey, pool, projectId, (myGen, hook, futureRef) -> {
            if (target != null) {
                storeProofResult(scopeKey, myGen, MethodStatus.CHECKING, projectId);
                refreshCodeLenses();
            } else {
                markEscChecking(uri, myGen, projectId);
            }
            try {
                CheckRunner.CheckResult result = task.apply(hook);
                if (result.isCommandLineError()) {
                    reportCommandLineError(result.diagnostics()); return;
                }
                if (target == null && !isCurrentSession(scopeKey, myGen)) return;

                if (result.isInternalError()) {
                    ServerLog.serverLog("[OpenJML] ESC for method: internal error (exit code " + result.exitCode() + ")");
                    publishMerged(uri);
                    if (target != null) {
                        storeProofResult(scopeKey, myGen, MethodStatus.CHECK_ERROR, projectId);
                        refreshCodeLenses();
                    }
                    return;
                }

                List<Diagnostic> diags = result.diagnostics();
                if (target != null) {
                    List<Diagnostic> newCheckPart = new ArrayList<>();
                    for (Diagnostic d : diags) {
                        if (!DiagnosticConverter.isEscVerificationFailure(d)) newCheckPart.add(d);
                    }
                    List<Diagnostic> keptCheck = new ArrayList<>(
                            checkDiags.getOrDefault(uri, List.of()));
                    keptCheck.removeIf(d -> target.contains(d.getRange().getStart().getLine()));
                    keptCheck.addAll(newCheckPart);
                    if (keptCheck.isEmpty()) checkDiags.remove(uri);
                    else checkDiags.put(uri, keptCheck);

                    IProverResult.Kind kind = result.proofResultForMethod(
                            CheckRunner.bareMethodName(target.rawName()));
                    Map<String, List<Diagnostic>> escByUri = new java.util.HashMap<>(
                            result.diagsByMethod().getOrDefault(target.rawName(), Map.of()));
                    int diagCount = escByUri.values().stream().mapToInt(List::size).sum();
                    MethodStatus ms = proofResultToStatus(kind, diagCount,
                                                          result.exitCode(), result.hasForeignErrors());
                    if (kind == IProverResult.UNSAT) {
                        Diagnostic hint = createVerifiedHintDiag(uri, target);
                        if (hint != null)
                            escByUri.computeIfAbsent(uri, k -> new java.util.ArrayList<>()).add(hint);
                    }
                    storeProofResult(scopeKey, myGen, ms, java.util.Collections.unmodifiableMap(escByUri), projectId);
                } else {
                    updateEscStatus(uri, result.proofResults(), result.exitCode(),
                                        result.foreignMessages(), myGen, result.diagsByMethod(), projectId);
                    result.diagsByMethod().keySet().stream()
                            .filter(diagUri -> !diagUri.equals(uri))
                            .forEach(diagUri -> publishMerged(diagUri));
                }
                publishMerged(uri);
                refreshCodeLenses();
            } catch (Throwable t) {
                ServerLog.serverLog("[OpenJML] ESC for method failed unexpectedly: " + t);
                if (target != null) {
                    storeProofResult(scopeKey, myGen, MethodStatus.UNKNOWN, projectId);
                    refreshCodeLenses();
                }
            }
        });
    }

    // --- disk file-change handlers (called from OpenJMLWorkspaceService) ---

    /**
     * Called when a {@code .jml} file changes on disk outside the editor.
     * If the file is already open in the editor the editor path handles it and
     * this method returns immediately to avoid a double-check.
     */
    public void handleWatchedJmlChange(String uri, FileChangeType type) {
        if (lastContent.containsKey(uri)) return;  // editor path already handles it

        if (type == FileChangeType.Deleted) {
            String javaUri = resolveCompanionJavaUri(uri, "");
            if (javaUri != null) {
                CheckRunner.getASTCache().remove(javaUri);
                if (client != null)
                    client.publishDiagnostics(new PublishDiagnosticsParams(javaUri, List.of()));
            }
            CheckRunner.getASTCache().remove(uri);
            setNavDirtyForUri(uri);
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
        // projectId unavailable from the watched-files protocol event; null triggers uri lookup.
        scheduleCheckNow(javaUri, javaContent, null);
    }

    /**
     * Called when a {@code .java} file is created or deleted on disk outside the editor.
     * Deleted files have their AST cache entry and diagnostics cleared.
     * Created files mark the nav cache dirty so the next navigation operation
     * or explicit index command re-runs the full project check.
     * Changed-but-not-open files are ignored — the user opens the file to trigger a check.
     */
    public void handleWatchedJavaChange(String uri, FileChangeType type) {
        if (lastContent.containsKey(uri)) return;  // editor handles it
        if (type == FileChangeType.Deleted) {
            CheckRunner.getASTCache().remove(uri);
            if (client != null)
                client.publishDiagnostics(new PublishDiagnosticsParams(uri, List.of()));
        } else if (type == FileChangeType.Created) {
            setNavDirtyForUri(uri);
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
            ServerLog.serverLog("[OpenJML] readFileFromDisk failed for " + path + ": " + e);
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

    private void scheduleCheckNow(String uri, String content, String projectId) {
        // Skip files that don't belong to any configured project (e.g. non-JML-natured
        // Eclipse projects, or files outside all workspace roots).
        OpenJMLSettings s = projectId != null ? settingsForProject(projectId) : settingsForUri(uri);
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

    private void scheduleCheckFile(String uri, String projectId) {
        // If the nav cache is clean, the project-wide check already covered all files
        // with current content.  Saves do not change in-memory content, so re-checking
        // here would only create a new IAPI context that invalidates the nav context.
        String filePid = projectId != null ? projectId : projectIdForUri(uri);
        AtomicBoolean fileDirty = filePid != null ? projectNavDirty.get(filePid) : null;
        if (fileDirty != null && !fileDirty.get()) return;
        OpenJMLSettings s = filePid != null ? settingsForProject(filePid) : settingsForUri(uri);
        if (s == null) return;
        // .jml files are spec files; redirect check to companion .java.
        // Use content-based check so companion diagnostics (including .jml markers) are updated.
        if (uri.endsWith(".jml")) {
            String javaUri = resolveCompanionJavaUri(uri, null);
            if (javaUri == null) return;
            String javaContent = lastContent.get(javaUri);
            final OpenJMLSettings fS = s;
            if (javaContent != null) {
                executor.submit(() -> runCheckContent(javaUri, javaContent, fS));
            } else {
                // java file not open; fall back to file-based check for java
                scheduleCheckFile(javaUri, filePid);
            }
            return;
        }
        // For .java files: use in-memory content if open, otherwise null (read from disk by OpenJML).
        // Both paths go through runCheckContent so dirty editors are always included.
        final String c = lastContent.get(uri);
        final OpenJMLSettings fS = s;
        executor.submit(() -> runCheckContent(uri, c, fS));
    }

    private void scheduleEscFile(String uri, OpenJMLSettings s, String projectId) {
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath == null) return;
        scheduleEscForPaths(List.of(filePath), s, projectId);
    }

    private void onEscMethodCompleted(String uri,
                                      org.jmlspecs.openjml.JmlTree.JmlMethodDecl methodDecl,
                                      org.openjml.IProverResult.Kind kind,
                                      java.util.Map<String, java.util.List<org.eclipse.lsp4j.Diagnostic>> methodDiags) {
        String methodName = methodDecl.name != null ? methodDecl.name.toString() : "?";
        int totalMethodDiags = methodDiags.values().stream().mapToInt(java.util.List::size).sum();
        ServerLog.serverLog("[onEscMethodCompleted] uri=" + uri + " method=" + methodName
                + " kind=" + kind + " methodDiags=" + totalMethodDiags
                + " methodDiagUris=" + methodDiags.keySet());
        String content = lastContent.get(uri);
        if (content == null) {
            ServerLog.serverLog("[onEscMethodCompleted] EARLY RETURN — no content for uri=" + uri);
            return;
        }

        // Compute line range directly from AST positions — avoids AST cache dependency
        // (the shared cache is only populated after the full run completes).
        int startLine = Math.max(0, offsetToLine(content, methodDecl.pos));
        int endLine = (methodDecl.body != null && methodDecl.body.endpos >= 0)
                ? Math.max(startLine, offsetToLine(content, methodDecl.body.endpos))
                : startLine;

        String rawName = (methodDecl.sym != null)
                ? org.jmlspecs.openjml.Utils.uniqueSymbolName(methodDecl.sym)
                : methodDecl.name.toString();
        String name = methodDecl.name.toString();

        java.util.Map<String, java.util.List<Diagnostic>> byUri = new java.util.HashMap<>(methodDiags);
        int diagCount = byUri.values().stream().mapToInt(List::size).sum();
        MethodStatus ms = proofResultToStatus(kind, diagCount, 0, false);
        if (kind == org.openjml.IProverResult.UNSAT) {
            String[] lines = content.split("\n", -1);
            if (startLine < lines.length) {
                String lineText = lines[startLine];
                int col = lineText.indexOf(name);
                if (col < 0) col = 0;
                Diagnostic hint = new Diagnostic(
                        new Range(new Position(startLine, col),
                                  new Position(startLine, col + name.length())),
                        "Verified", DiagnosticSeverity.Hint, DiagnosticConverter.SOURCE_ESC);
                byUri.computeIfAbsent(uri, k -> new java.util.ArrayList<>()).add(hint);
            }
        }
        RunningSession rs = runningSessions.get(uri);
        long gen = rs != null ? rs.sessionGen() : sessionCounter.get();
        int storedDiags = byUri.values().stream().mapToInt(java.util.List::size).sum();
        ServerLog.serverLog("[onEscMethodCompleted] storing key=" + uri + "#" + rawName
                + " gen=" + gen + " status=" + ms.label() + " byUriDiags=" + storedDiags
                + " byUriKeys=" + byUri.keySet());
        storeProofResult(uri + "#" + rawName, gen, ms, java.util.Collections.unmodifiableMap(byUri), null);
        executor.execute(() -> { publishMerged(uri); refreshCodeLenses(); });
    }

    /** Converts a character offset to a 0-based line number in the given content. */
    private static int offsetToLine(String content, int offset) {
        if (offset <= 0) return 0;
        int line = 0;
        int limit = Math.min(offset, content.length());
        for (int i = 0; i < limit; i++) {
            if (content.charAt(i) == '\n') line++;
        }
        return line;
    }


    /** Body of an ESC pool task: receives the generation counter, the IAPI hook,
     *  and the batch-future reference for sub-session registration. */
    @FunctionalInterface
    private interface EscJobBody {
        void run(long myGen, java.util.function.Consumer<IAPI> hook,
                 java.util.concurrent.atomic.AtomicReference<Future<?>> futureRef);
    }

    /**
     * Common session-management wrapper for all ESC pool submissions.
     *
     * <p>Cancels any running session for {@code key}, submits {@code body} to
     * {@code pool}, and registers the new session in {@link #runningSessions}.
     * The IAPI hook wired to the session is passed to {@code body} so that
     * {@link CheckRunner} can hand back the live {@link IAPI} once it is created.
     * {@link #debugContent} is called at the start and end of the task.
     */
    private void submitEscJob(String key, ExecutorService pool, String projectId, EscJobBody body) {
        RunningSession prev = runningSessions.remove(key);
        if (prev != null) {
            prev.future().cancel(false);
            IAPI prevApi = prev.api().get();
            if (prevApi != null) prevApi.cancelEsc();
        }
        var futureRef = new java.util.concurrent.atomic.AtomicReference<Future<?>>();
        var apiRef    = new java.util.concurrent.atomic.AtomicReference<IAPI>();
        Future<?> f = pool.submit(() -> {
            long myGen = sessionCounter.incrementAndGet();
            runningSessions.put(key, new RunningSession(myGen, futureRef.get(), apiRef, true, projectId));
            java.util.function.Consumer<IAPI> hook = api -> {
                apiRef.set(api);
                RunningSession rs = runningSessions.get(key);
                if (rs != null) rs.api().set(api);
            };
            try {
                body.run(myGen, hook, futureRef);
            } finally {
                runningSessions.remove(key);
            }
        });
        futureRef.set(f);
        runningSessions.putIfAbsent(key, new RunningSession(-1L, f, apiRef, true, projectId));
    }



    // --- runners (execute on the thread pool) ---

    // INVARIANT: the check runners below update checkDiags and publish merged
    // diagnostics, but they MUST NOT touch proofResults or call
    // refreshCodeLenses().  Partially-typed code during editing must not disturb
    // the ESC code-lens status that the user sees.

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

    // -----------------------------------------------------------------------
    // Per-project nav cache management
    // -----------------------------------------------------------------------

    /**
     * Ensure per-project nav state exists for every configured project.
     * Called before any schedule/wait operation so that dirty flags and locks
     * are available without a ConcurrentHashMap.computeIfAbsent on the hot path.
     */
    private void initProjectNavState() {
        if (globalSettings.projects != null && !globalSettings.projects.isEmpty()) {
            for (ProjectConfig cfg : globalSettings.projects) {
                projectNavDirty.computeIfAbsent(cfg.id, k -> new AtomicBoolean(true));
                projectNavLocks.computeIfAbsent(cfg.id, k -> new Object());
            }
        } else {
            projectNavDirty.computeIfAbsent(
                    OpenJMLSettings.WORKSPACE_PROJECT_ID, k -> new AtomicBoolean(true));
            projectNavLocks.computeIfAbsent(
                    OpenJMLSettings.WORKSPACE_PROJECT_ID, k -> new Object());
        }
    }

    /**
     * Returns the configured source roots for the given project, or an empty
     * list if the project is not found.
     */
    private List<String> rootsForProject(String projectId) {
        if (globalSettings.projects != null) {
            for (ProjectConfig cfg : globalSettings.projects) {
                if (projectId != null && projectId.equals(cfg.id))
                    return cfg.rootPaths != null ? cfg.rootPaths : List.of();
            }
        }
        if (OpenJMLSettings.WORKSPACE_PROJECT_ID.equals(projectId))
            return globalSettings.effectiveRoots();
        return List.of();
    }

    /**
     * Mark the nav dirty flag for the project that owns {@code uri}.
     * No-op if the URI does not belong to any configured project.
     */
    private void setNavDirtyForUri(String uri) {
        String pid = projectIdForUri(uri);
        if (pid == null) return;
        AtomicBoolean d = projectNavDirty.get(pid);
        if (d != null) d.set(true);
    }

    /**
     * Blocking: run project checks for {@code projectId} until the nav-dirty
     * flag is stable (false), then rebuild the declaration index once.
     *
     * <p>Holds the per-project lock for the entire duration so that at most
     * one check runs per project at a time.  If {@link #didChange} sets the
     * dirty flag while a check is running, the loop detects this on the next
     * iteration and runs another check before rebuilding.
     *
     * <p>If {@code projectId} is {@code null}, updates all configured projects.
     */
    private void requestNavUpdate(String projectId) {
        if (projectId == null) {
            // Update every project.
            if (globalSettings.projects != null && !globalSettings.projects.isEmpty()) {
                for (ProjectConfig cfg : globalSettings.projects)
                    requestNavUpdate(cfg.id);
            } else {
                requestNavUpdate(OpenJMLSettings.WORKSPACE_PROJECT_ID);
            }
            return;
        }
        Object lock = projectNavLocks.computeIfAbsent(projectId, k -> new Object());
        AtomicBoolean dirty = projectNavDirty.computeIfAbsent(
                projectId, k -> new AtomicBoolean(true));
        synchronized (lock) {
            while (dirty.compareAndSet(true, false)) {
                runProjectCheck(projectId);
            }
            // Nav is now stable: rebuild the declaration index once.
            CheckRunner.getASTCache().rebuildNavIndex(projectId);
        }
    }

    /**
     * Run a {@code --check} pass for the given project and store diagnostics.
     * Does NOT rebuild the nav index (that is the caller's responsibility).
     */
    private void runProjectCheck(String projectId) {
        List<String> roots = rootsForProject(projectId);
        if (roots.isEmpty()) return;
        OpenJMLSettings s = settingsForProject(projectId);
        Map<String, String> snapshot = dirtySnapshot();
        try {
            CheckRunner.DirCheckResult result =
                    CheckRunner.runCheckDirWithContext(roots, snapshot, s, projectId);
            result.diagnosticsByUri().forEach((diagUri, diags) -> {
                storeCheckDiags(diagUri, diags);
                publishMerged(diagUri);
            });
            lastCheckedContent.putAll(snapshot);
        } catch (Throwable t) {
            ServerLog.serverLog("[runProjectCheck] error: " + t);
        }
    }

    /**
     * Returns a future that completes once the nav cache for {@code projectId}
     * is up to date.  If the cache is already clean and no check is running,
     * the returned future may complete immediately.
     *
     * <p>If {@code projectId} is {@code null}, waits for all configured projects.
     */
    private CompletableFuture<Void> waitForProjectNav(String projectId) {
        return CompletableFuture.runAsync(() -> requestNavUpdate(projectId), executor);
    }

    /**
     * Ensure the project-wide nav cache is up to date before a navigation
     * operation.  Returns a future that completes when all projects are clean.
     */
    private CompletableFuture<Void> ensureNavCacheReady() {
        return waitForProjectNav(null);
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
        String pid = projectIdForUri(primaryUri);
        AtomicBoolean pidDirty = pid != null ? projectNavDirty.get(pid) : null;
        CompletableFuture<Void> checkFuture;
        if (pidDirty != null && pidDirty.get()) {
            ServerLog.serverLog("[ensureFreshAndConfirm] op=" + operationName
                    + " uri=" + primaryUri + " pid=" + pid + " — nav dirty, updating");
            checkFuture = waitForProjectNav(pid);
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

            return client.showMessageRequest(req).thenApply(action -> {
                if (action != null) return "Proceed Anyway".equals(action.getTitle());
                // null means the client dismissed or does not support showMessageRequest.
                clientLog(operationName + " aborted: workspace has compilation errors"
                        + " and client returned no response to the confirmation dialog.");
                return false;
            });
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
        if (uri.endsWith(".jml")) { ServerLog.serverLog("[runCheckContent] early return for .jml uri=" + uri); return; }
        Map<String, String> snapshot = dirtySnapshot();
        ServerLog.serverLog("[runCheckContent] uri=" + uri + " content=" + (content == null ? "null(disk)" : "present") + " dirtySnapshot=" + snapshot.keySet());
        if (content != null) lastCheckedContent.put(uri, content);
        try {
            // Snapshot lastContent at execution time so that concurrent edits do not
            // mutate the context map while OpenJML is parsing it.
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
            // Do NOT call refreshCodeLenses() here — that would disturb ESC code-lens
            // status, which is managed separately by ESC callbacks.  However, notify
            // the client that semantic tokens have changed so it re-queries using the
            // newly cached AST (upgrading from the initial regex fallback to AST-based
            // coloring).
            refreshSemanticTokens();
        } catch (Throwable t) {
            ServerLog.serverLog("[OpenJML] check failed for " + uri + ": " + t);
        }
    }


    // --- ESC code-lens status helpers ---

    /** Set all detected methods in {@code uri} to the given {@code status}. */
    private void markAllMethodStatus(String uri, MethodStatus status, long gen, String projectId) {
        String content = lastContent.get(uri);
        if (content == null) return;
        ASTCache.Entry markAstEntry = CheckRunner.getASTCache().get(uri);
        List<JavaSourceScanner.MethodInfo> methods = (markAstEntry != null)
                ? JavaSourceScanner.findMethodsFromAst(markAstEntry.ast())
                : List.of();
        if (methods.isEmpty()) return;
        for (JavaSourceScanner.MethodInfo m : methods) {
            storeProofResult(methodKey(uri, m), gen, status, projectId);
        }
    }

    /** Mark all detected methods in {@code uri} as currently being checked. */
    /**
     * Set the code lens status for a single method (identified by simple name)
     * to CHECKING, then refresh code lenses.  Called when the prover sends a
     * RUNNING notification for that method so the lens updates before the result
     * arrives.  If multiple overloaded methods share the name, all are marked.
     * The gen is looked up from {@link #runningSessions} so callers do not need
     * to capture it explicitly.
     */
    private void markMethodCheckingByName(String uri, String methodName, long gen, String projectId) {
        String content = lastContent.get(uri);
        if (content == null) return;
        ASTCache.Entry markCheckAstEntry = CheckRunner.getASTCache().get(uri);
        List<JavaSourceScanner.MethodInfo> markCheckMethods = (markCheckAstEntry != null)
                ? JavaSourceScanner.findMethodsFromAst(markCheckAstEntry.ast())
                : List.of();
        boolean changed = false;
        for (JavaSourceScanner.MethodInfo m : markCheckMethods) {
            if (m.name().equals(methodName)) {
                storeProofResult(methodKey(uri, m), gen, MethodStatus.CHECKING, projectId);
                changed = true;
            }
        }
        if (changed) {
            refreshCodeLenses();
        }
    }

    private void markEscChecking(String uri, long gen, String projectId) {
        markAllMethodStatus(uri, MethodStatus.CHECKING, gen, projectId);
        refreshCodeLenses();
    }

    /**
     * Update per-method ESC status for {@code uri}.
     *
     * <p>Exit codes: 0 = success (UNSAT/INFEASIBLE expected), 1 = syntax/type
     * errors (CHECK_ERROR for any method with no proof result), 6 = verification
     * failures (SAT/POSSIBLY_SAT/SKIPPED/TIMEOUT/CANCELLED/UNKNOWN/ERROR).
     */
    private void updateEscStatus(String uri,
                                 Map<String, IProverResult.Kind> escProofResults, int exitCode,
                                 List<String> foreignFiles, long gen,
                                 Map<String, Map<String, List<Diagnostic>>> diagsByMethod,
                                 String projectId) {
        // ESC always produces an attributed AST.  Single-file ESC stores it in the live
        // cache; project/folder ESC stores it in a nav section.  getNav() checks both.
        ASTCache.Entry astEntry = CheckRunner.getASTCache().getNav(uri);
        if (astEntry == null) {
            ServerLog.serverLog("[OpenJML] updateEscStatus: no AST for " + uri + " — skipping");
            return;
        }
        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(astEntry.ast());
        if (methods.isEmpty()) return;

        boolean hasForeignErrors = !foreignFiles.isEmpty();
        for (JavaSourceScanner.MethodInfo m : methods) {
            if (!m.sourceUri().isEmpty() && !m.sourceUri().equals(uri)) continue;
            IProverResult.Kind kind = CheckRunner.lookupResult(escProofResults, m.rawName());
            Map<String, List<Diagnostic>> byUri = new java.util.HashMap<>(
                    diagsByMethod.getOrDefault(m.rawName(), Map.of()));
            int diagCount = byUri.values().stream().mapToInt(List::size).sum();
            MethodStatus ms = proofResultToStatus(kind, diagCount, exitCode, hasForeignErrors);
            if (kind == IProverResult.UNSAT) {
                Diagnostic hint = createVerifiedHintDiag(uri, m);
                if (hint != null)
                    byUri.computeIfAbsent(uri, k -> new java.util.ArrayList<>()).add(hint);
            }
            storeProofResult(methodKey(uri, m), gen, ms, java.util.Collections.unmodifiableMap(byUri), projectId);
        }

        // Also update .jml companion files whose model methods were proved in this run.
        // These files have their own code-lens status maps, keyed by .jml line numbers,
        // which require a separate findMethodsFromAst call on the .jml AST.
        java.util.Set<String> jmlUris = new java.util.LinkedHashSet<>();
        for (JavaSourceScanner.MethodInfo m : methods) {
            if (!m.sourceUri().isEmpty() && !m.sourceUri().equals(uri)
                    && m.sourceUri().endsWith(".jml"))
                jmlUris.add(m.sourceUri());
        }
        for (String jmlUri : jmlUris) {
            updateJmlEscStatus(jmlUri, escProofResults, exitCode, hasForeignErrors, gen, diagsByMethod, projectId);
        }

        refreshCodeLenses();

        if (hasForeignErrors) {
            String fileName = uri.substring(uri.lastIndexOf('/') + 1);
            clientLog("OpenJML: ESC on " + fileName
                    + " could not run — type errors in: " + String.join(", ", foreignFiles));
        }
    }

    /**
     * Update per-method ESC status for a companion {@code .jml} file after ESC ran on
     * the associated {@code .java} file.
     *
     * <p>Uses the {@code .jml} AST from the cache (stored there by {@code cacheSpecsCu}
     * during the prior {@code --check} pass) so that method positions are correct for
     * the {@code .jml} editor.  If the {@code .jml} file is not open
     * ({@link #lastContent} has no entry for it), this is a no-op.
     */
    private void updateJmlEscStatus(String jmlUri,
                                    Map<String, IProverResult.Kind> escProofResults,
                                    int exitCode, boolean hasForeignErrors, long gen,
                                    Map<String, Map<String, List<Diagnostic>>> diagsByMethod,
                                    String projectId) {
        ASTCache.Entry jmlEntry = CheckRunner.getASTCache().get(jmlUri);
        if (jmlEntry == null) return;

        List<JavaSourceScanner.MethodInfo> jmlMethods =
                JavaSourceScanner.findMethodsFromAst(jmlEntry.ast());
        if (jmlMethods.isEmpty()) return;

        for (JavaSourceScanner.MethodInfo m : jmlMethods) {
            IProverResult.Kind kind = CheckRunner.lookupResult(escProofResults, m.rawName());
            Map<String, List<Diagnostic>> byUri = new java.util.HashMap<>(
                    diagsByMethod.getOrDefault(m.rawName(), Map.of()));
            int diagCount = byUri.values().stream().mapToInt(List::size).sum();
            MethodStatus ms = proofResultToStatus(kind, diagCount, exitCode, hasForeignErrors);
            if (kind == IProverResult.UNSAT) {
                Diagnostic hint = createVerifiedHintDiag(jmlUri, m);
                if (hint != null)
                    byUri.computeIfAbsent(jmlUri, k -> new java.util.ArrayList<>()).add(hint);
            }
            storeProofResult(methodKey(jmlUri, m), gen, ms, java.util.Collections.unmodifiableMap(byUri), projectId);
        }
        publishMerged(jmlUri);
    }

    private Diagnostic createVerifiedHintDiag(String uri, JavaSourceScanner.MethodInfo m) {
        String content = lastContent.get(uri);
        if (content == null) return null;
        String[] lines = content.split("\n", -1);
        int line = m.startLine();
        if (line >= lines.length) return null;
        String lineText = lines[line];
        int col = lineText.indexOf(m.name());
        if (col < 0) col = 0;
        int endCol = col + m.name().length();
        Range range = new Range(new Position(line, col), new Position(line, endCol));
        return new Diagnostic(range, "Verified", DiagnosticSeverity.Hint, DiagnosticConverter.SOURCE_ESC);
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
     * @param partialProofResults proof results for methods that have finished so far
     * @param diagsByMethod       per-method diagnostics collected so far (method FQN → URI → diags)
     */
    private void updateEscStatusPartial(String uri,
            Map<String, IProverResult.Kind> partialProofResults, long gen,
            Map<String, Map<String, List<Diagnostic>>> diagsByMethod, String projectId) {
        ASTCache.Entry astEntry = CheckRunner.getASTCache().get(uri);
        if (astEntry == null) return;
        List<JavaSourceScanner.MethodInfo> methods =
                JavaSourceScanner.findMethodsFromAst(astEntry.ast());
        if (methods.isEmpty()) return;
        ServerLog.serverLog("[updateEscStatusPartial] uri=" + uri
                + " partialResults=" + partialProofResults.size()
                + " methods=" + methods.size());
        java.util.Set<String> jmlUris = new java.util.LinkedHashSet<>();
        for (JavaSourceScanner.MethodInfo m : methods) {
            if (!m.sourceUri().isEmpty() && !m.sourceUri().equals(uri)) {
                if (m.sourceUri().endsWith(".jml")) jmlUris.add(m.sourceUri());
                continue;
            }
            IProverResult.Kind kind = CheckRunner.lookupResult(partialProofResults, m.rawName());
            if (kind == null) continue;   // not yet proven — leave as CHECKING
            Map<String, List<Diagnostic>> byUri = new java.util.HashMap<>(
                    diagsByMethod.getOrDefault(m.rawName(), Map.of()));
            int diagCount = byUri.values().stream().mapToInt(List::size).sum();
            MethodStatus status = proofResultToStatus(kind, diagCount, 0, false);
            if (kind == IProverResult.UNSAT) {
                Diagnostic hint = createVerifiedHintDiag(uri, m);
                if (hint != null) byUri.computeIfAbsent(uri, k -> new java.util.ArrayList<>()).add(hint);
            }
            ServerLog.serverLog("[updateEscStatusPartial] method=" + m.rawName()
                    + " kind=" + kind + " status=" + status.label() + " diagCount=" + diagCount);
            storeProofResult(methodKey(uri, m), gen, status, java.util.Collections.unmodifiableMap(byUri), projectId);
        }

        // Propagate partial results to open .jml companion editors.
        for (String jmlUri : jmlUris) {
            ASTCache.Entry jmlEntry = CheckRunner.getASTCache().get(jmlUri);
            if (jmlEntry == null) continue;
            List<JavaSourceScanner.MethodInfo> jmlMethods =
                    JavaSourceScanner.findMethodsFromAst(jmlEntry.ast());
            for (JavaSourceScanner.MethodInfo m : jmlMethods) {
                IProverResult.Kind kind = CheckRunner.lookupResult(partialProofResults, m.rawName());
                if (kind == null) continue;
                Map<String, List<Diagnostic>> byUri = new java.util.HashMap<>(
                        diagsByMethod.getOrDefault(m.rawName(), Map.of()));
                int diagCount = byUri.values().stream().mapToInt(List::size).sum();
                MethodStatus status = proofResultToStatus(kind, diagCount, 0, false);
                if (kind == IProverResult.UNSAT) {
                    Diagnostic hint = createVerifiedHintDiag(jmlUri, m);
                    if (hint != null) byUri.computeIfAbsent(jmlUri, k -> new java.util.ArrayList<>()).add(hint);
                }
                storeProofResult(methodKey(jmlUri, m), gen, status, java.util.Collections.unmodifiableMap(byUri), projectId);
            }
        }
    }

    /**
     * Convert a proof result kind to a {@link MethodStatus}.
     *
     * @param kind             proof result kind, or {@code null} if none was recorded
     * @param diagCount        number of diagnostics attributed to this method's proof
     * @param exitCode         OpenJML exit code: 0=ok, 1=syntax/type errors, 6=verification failures
     * @param hasForeignErrors true when errors in other files caused the failure
     */
    private static MethodStatus proofResultToStatus(IProverResult.Kind kind,
                                                     int diagCount, int exitCode,
                                                     boolean hasForeignErrors) {
        if (kind == IProverResult.UNSAT) {
            return MethodStatus.VERIFIED;
        } else if (kind == IProverResult.INFEASIBLE) {
            return MethodStatus.INFEASIBLE;
        } else if (kind == IProverResult.SAT || kind == IProverResult.POSSIBLY_SAT
                || kind == IProverResult.UNKNOWN || kind == IProverResult.ERROR) {
            int issues = Math.max(kind == IProverResult.SAT
                    || kind == IProverResult.POSSIBLY_SAT ? 1 : 0, diagCount);
            return MethodStatus.notVerified(issues);
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
        refreshSemanticTokens();
    }

    private void refreshSemanticTokens() {
        if (client != null && clientSupportsSemanticTokenRefresh) client.refreshSemanticTokens();
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
    // --- command-line error reporting ---

    /**
     * Reports an exit-code-2 (bad command-line argument) failure to the user.
     * The message includes any diagnostic text that OpenJML produced and directs
     * the user to the Preferences page to review option values.
     */
    private void reportCommandLineError(List<Diagnostic> diagnostics) {
        if (client == null) return;
        String detail = diagnostics.stream()
                .map(d -> {
                    var m = d.getMessage();
                    if (m == null) return null;
                    if (m.isLeft())  return m.getLeft();
                    if (m.isRight() && m.getRight() != null) return m.getRight().getValue();
                    return null;
                })
                .filter(m -> m != null && !m.isBlank())
                .collect(java.util.stream.Collectors.joining("\n"));
        String msg = "OpenJML rejected a command-line option (exit code 2). "
                + "Check the OpenJML preference settings for invalid values."
                + (detail.isBlank() ? "" : "\n\n" + detail);
        clientErrorPrefs(msg, "settings");
    }

    // --- client console / action message helpers ---

    /**
     * Send an Info-level message to the client (shown timestamped in the JML Console).
     * Never triggers a dialog — use this for normal operational summaries.
     */
    private void clientLog(String message) {
        if (client == null) return;
        client.logMessage(new MessageParams(MessageType.Info, message));
    }

    /**
     * Send an Error-level message with an acknowledgement dialog (dismiss only).
     * Use for unexpected runtime failures (exceptions, protocol errors) that the
     * user should see but cannot directly act on.
     */
    private void clientError(String message) {
        sendActionMessage(1, message, List.of(dismiss()));
    }

    /**
     * Send a Warning-level message with an "Open Preferences" + dismiss dialog.
     * Use when the cause is likely a misconfigured option.
     *
     * @param target  preference target: {@code "toolOptions"} or {@code "settings"}
     */
    private void clientWarnPrefs(String message, String target) {
        sendActionMessage(2, message, List.of(openPrefs(target), dismiss()));
    }

    /**
     * Send an Error-level message with an "Open Preferences" + dismiss dialog.
     * Use when the cause is definitely a bad configuration value.
     *
     * @param target  preference target: {@code "toolOptions"} or {@code "settings"}
     */
    private void clientErrorPrefs(String message, String target) {
        sendActionMessage(1, message, List.of(openPrefs(target), dismiss()));
    }

    /**
     * Core send method. If the client declared {@code supportsActionMessages},
     * sends {@code $/openjml/actionMessage}; otherwise falls back to
     * {@code window/logMessage} so generic clients still see the text.
     */
    private void sendActionMessage(int type, String message,
                                   List<ActionMessageParams.ActionItem> actions) {
        if (client == null) return;
        if (clientSupportsActionMessages) {
            // Always send the notification so the client logs the message to its console.
            // But suppress the dialog actions for repeated messages — the same warning
            // (e.g. an unrecognised --warn key) would otherwise pop up on every
            // per-file or per-method ESC sub-pass.
            boolean firstOccurrence = shownDialogMessages.add(message);
            var p = new ActionMessageParams();
            p.type    = type;
            p.message = message;
            p.actions = firstOccurrence ? actions : List.of();
            ((org.eclipse.lsp4j.jsonrpc.Endpoint) client).notify(
                    "$/openjml/actionMessage", p);
        } else {
            // Fallback for generic clients: plain window/logMessage, no dialog.
            MessageType mt = switch (type) {
                case 1  -> MessageType.Error;
                case 2  -> MessageType.Warning;
                case 4  -> MessageType.Log;
                default -> MessageType.Info;
            };
            client.logMessage(new MessageParams(mt, message));
        }
    }

    /** Factory: a "dismiss / OK" action item. */
    private static ActionMessageParams.ActionItem dismiss() {
        var a = new ActionMessageParams.ActionItem();
        a.kind  = "dismiss";
        a.title = "OK";
        return a;
    }

    /** Factory: an "Open Preferences" action item for the given target page. */
    private static ActionMessageParams.ActionItem openPrefs(String target) {
        var a = new ActionMessageParams.ActionItem();
        a.kind   = "openPreferences";
        a.target = target;
        a.title  = "Open Preferences";
        return a;
    }

    private void publishDiags(String uri, List<Diagnostic> diags) {
        if (client == null) return;
        client.publishDiagnostics(new PublishDiagnosticsParams(uri, diags));
        if (diags.isEmpty()) markedUris.remove(uri);
        else                 markedUris.add(uri);
    }

    /**
     * Store CHECK or RAC results for {@code uri}.  Replaces {@code checkDiags}
     * for the URI.
     */
    private void storeCheckDiags(String uri, List<Diagnostic> diags) {
        if (diags.isEmpty()) checkDiags.remove(uri);
        else checkDiags.put(uri, diags);
    }

    private void publishMerged(String uri) {
        List<Diagnostic> checkList = checkDiags.getOrDefault(uri, List.of());
        List<Diagnostic> escList = new ArrayList<>();
        proofResults.values().forEach(pr -> escList.addAll(pr.byUri().getOrDefault(uri, List.of())));
        ServerLog.serverLog("[publishMerged] uri=" + uri
                + " checkDiags=" + checkList.size() + " escDiags=" + escList.size()
                + " proofResultCount=" + proofResults.size()
                + " proofResultsWithDiags=" + proofResults.values().stream()
                        .filter(pr -> !pr.byUri().getOrDefault(uri, List.of()).isEmpty()).count());
        List<Diagnostic> merged = new ArrayList<>();
        merged.addAll(checkList);
        merged.addAll(escList);
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
     * Abort the SMT proof for one specific method, then allow the ESC loop to
     * continue with the next method.  Unlike {@link #cancelEsc(String)}, this
     * does not cancel the overall ESC run.
     *
     * <p>{@code rawName} is the fully-qualified method name as returned by
     * {@code Utils.uniqueSymbolName()} (e.g., {@code "com.example.Foo.add(int,int)"}).
     * The method searches {@link #runningSessions} for any key whose suffix after
     * {@code '#'} equals {@code rawName}.
     *
     * <p>When {@code rawName} is {@code null} or empty, all currently-active proofs
     * are aborted (same effect as a broad "skip current" across all parallel runs).
     */
    void abortMethodProof(String uri, String rawName) {
        if (uri != null && !uri.isEmpty() && rawName != null && !rawName.isEmpty()) {
            // Construct "uri#rawName" so abortMethodProofForKey can find either a
            // per-method session (split-by-method) or fall back to the file-level
            // session registered during the RUNNING event (file-level ESC).
            abortMethodProofForKey(uri + "#" + rawName);
        } else if (rawName != null && !rawName.isEmpty()) {
            // No URI supplied — search all sessions for a key ending with "#rawName".
            String suffix = "#" + rawName;
            new ArrayList<>(runningSessions.keySet()).stream()
                    .filter(k -> k.endsWith(suffix))
                    .forEach(this::abortMethodProofForKey);
        } else {
            new ArrayList<>(runningSessions.keySet()).forEach(this::abortMethodProofForKey);
        }
    }

    private void abortMethodProofForKey(String key) {
        // Try the exact per-method session key first.
        RunningSession session = runningSessions.get(key);
        if (session != null) {
            IAPI api = session.api().get();
            if (api != null) {
                System.out.println("[OpenJML] abortMethodProof: found session API for " + key);
                api.abortCurrentProof();
                return;
            }
        }
        // For a method key (uri#rawName), fall back to the file-level session.
        if (key.contains("#")) {
            String uri = key.substring(0, key.indexOf('#'));
            RunningSession fileSession = runningSessions.get(uri);
            if (fileSession != null) {
                IAPI fileApi = fileSession.api().get();
                if (fileApi != null) {
                    System.out.println("[OpenJML] abortMethodProof: found file-level API for uri=" + uri);
                    fileApi.abortCurrentProof();
                } else {
                    System.out.println("[OpenJML] abortMethodProof: NO API found for uri=" + uri
                            + "; runningSessions keys=" + runningSessions.keySet());
                }
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
    void cancelEsc(String projectId, String target) {
        if (target != null && !target.isEmpty()) {
            abortEscForKey(target);
        } else {
            new ArrayList<>(runningSessions.keySet()).stream()
                    .filter(k -> matchesProject(k, projectId))
                    .forEach(this::abortEscForKey);
        }
    }

    /** Human-readable project label for logging (empty string → "(workspace)"). */
    private static String displayProject(String projectId) {
        if (projectId == null) return "(none)";
        if (projectId.isEmpty()) return "(workspace)";
        return projectId;
    }

    /** Returns true if {@code key} (a URI or "uri#method") belongs to {@code projectId},
     *  or if {@code projectId} is null (match all; used when project is unknown).
     *  A URI not covered by any configured project root returns null from
     *  {@link #projectIdForUri}, which is treated as "unknown project — match all"
     *  so that sessions whose project cannot be determined are always visible. */
    private boolean matchesProject(String key, String projectId) {
        if (projectId == null) return true;
        String uri = key.contains("#") ? key.substring(0, key.indexOf('#')) : key;
        String uriPid = projectIdForUri(uri);
        return uriPid == null || projectId.equals(uriPid);
    }

    private void abortEscForKey(String key) {
        RunningSession session = runningSessions.remove(key);
        // cancel(false): prevent a queued task from starting, but do NOT interrupt
        // a running thread.  Thread interruption causes SolverProcess sleeps to throw
        // "sleep interrupted" which surfaces as an ERROR diagnostic rather than CANCELLED.
        // The actual kill is handled by api.cancelEsc() below (destroyForcibly).
        if (session != null) {
            session.future().cancel(false);
            IAPI api = session.api().get();
            int k = key.lastIndexOf('/');
            String name = k == -1 ? key : key.substring(k+1);
            if (api != null) {
                ServerLog.serverLog("[OpenJML] ESC cancelled for " + name);
                api.cancelEsc();
            } else {
                ServerLog.serverLog("[OpenJML] ESC task cancelled (queued, not yet running) for " + name);
            }
        }
    }

    /**
     * Returns a snapshot of all currently-running ESC task keys.
     * Whole-file runs are identified by bare URI; per-method runs use
     * {@code "uri#methodName"} format.
     */
    List<String> getRunningEscUris() {
        return runningSessions.entrySet().stream()
                .filter(e -> e.getValue().visible())
                .map(Map.Entry::getKey)
                .collect(java.util.stream.Collectors.toList());
    }

    List<String> getRunningEscUrisForProject(String projectId) {
        return runningSessions.entrySet().stream()
                .filter(e -> e.getValue().visible())
                .filter(e -> projectId == null || projectId.equals(e.getValue().projectId()))
                .map(Map.Entry::getKey)
                .collect(java.util.stream.Collectors.toList());
    }

    /**
     * Clear all OpenJML diagnostic markers without scheduling any new checks.
     *
     * <p>Clears {@code checkDiags} and
     * {@code proofResults}, then publishes empty diagnostic lists for every
     * open file so the client removes the markers immediately.  Code lenses are
     * refreshed so per-method ESC status indicators reset to the idle state.
     *
     * <p>Pending and running checks are left undisturbed — they will overwrite
     * the now-empty markers when they complete.  Use {@link #resetAndReindex()}
     * instead when a full restart is needed.
     */
    private void debugContent(String label) {
        StringBuilder sb = new StringBuilder("[debugContent] ").append(label).append('\n');

        // globalSettings summary
        sb.append("  globalSettings: check=").append(globalSettings.clientSettings.checkTriggerOn)
          .append(" esc=").append(globalSettings.clientSettings.escTriggerOn)
          .append(" engine=").append(globalSettings.clientSettings.escEngine)
          .append(" javaMode=").append(globalSettings.effectiveJavaMode())
          .append(" incrementalSync=").append(globalSettings.clientSettings.incrementalSync).append('\n');

        // lastContent (open editors)
        sb.append("  lastContent (").append(lastContent.size()).append(" open file(s)):\n");
        lastContent.forEach((uri, c) ->
                sb.append("    ").append(uri).append(" (").append(c.length()).append(" chars)\n"));

        // dirtyUris
        sb.append("  dirtyUris (").append(dirtyUris.size()).append("):\n");
        dirtyUris.forEach(uri -> sb.append("    ").append(uri).append('\n'));

        // lastCheckedContent
        sb.append("  lastCheckedContent (").append(lastCheckedContent.size()).append(" file(s)):\n");
        lastCheckedContent.forEach((uri, c) ->
                sb.append("    ").append(uri).append(" (").append(c.length()).append(" chars)\n"));

        // ASTCache — live tier then nav sections
        ASTCache astCache = CheckRunner.getASTCache();
        var liveUris = new java.util.ArrayList<String>();
        astCache.forEach((uri, e) -> liveUris.add(uri));
        sb.append("  ASTCache live (").append(liveUris.size()).append(" file(s)):\n");
        liveUris.forEach(uri -> sb.append("    ").append(uri).append('\n'));

        astCache.forEachNavSection((pid, uris) -> {
            AtomicBoolean dirty = projectNavDirty.get(pid);
            sb.append("  ASTCache nav section=").append(pid)
              .append(" dirty=").append(dirty != null && dirty.get())
              .append(" (").append(uris.size()).append(" file(s)):\n");
            uris.forEach(uri -> sb.append("    ").append(uri).append('\n'));
        });

        // checkDiags and proofResults grouped by project (skip projects with no content)
        var checkByProject  = new java.util.LinkedHashMap<String, java.util.List<String>>();
        var proofByProject  = new java.util.LinkedHashMap<String, java.util.List<String>>();
        checkDiags.forEach((uri, diags) ->
                checkByProject.computeIfAbsent(
                        displayProject(projectIdForUri(uri)),
                        k -> new java.util.ArrayList<>())
                    .add(uri + " → " + diags.size() + " diag(s)"));
        proofResults.forEach((key, pr) -> {
            String uri = key.contains("#") ? key.substring(0, key.indexOf('#')) : key;
            int total = pr.byUri().values().stream().mapToInt(List::size).sum();
            proofByProject.computeIfAbsent(
                        displayProject(projectIdForUri(uri)),
                        k -> new java.util.ArrayList<>())
                    .add(key + " status=" + pr.status() + " diags=" + total);
        });
        var allProjects = new java.util.LinkedHashSet<String>();
        allProjects.addAll(checkByProject.keySet());
        allProjects.addAll(proofByProject.keySet());
        for (String pid : allProjects) {
            var cd = checkByProject.getOrDefault(pid, List.of());
            var pr = proofByProject.getOrDefault(pid, List.of());
            sb.append("  project=").append(pid)
              .append(" checkDiags=").append(cd.size())
              .append(" proofResults=").append(pr.size()).append(":\n");
            cd.forEach(line -> sb.append("    check: ").append(line).append('\n'));
            pr.forEach(line -> sb.append("    proof: ").append(line).append('\n'));
        }

        // markedUris
        sb.append("  markedUris (").append(markedUris.size()).append("):\n");
        markedUris.forEach(uri -> sb.append("    ").append(uri).append('\n'));

        ServerLog.serverLog(sb.toString());
    }

    void clearMarkers() {
        ServerLog.serverLog("[clearMarkers] clearing all markers; markedUris=" + markedUris.size()
                + " checkDiags=" + checkDiags.size() + " proofResults=" + proofResults.size()
                + (markedUris.isEmpty() ? " (no markers to clear)" : ""));
        checkDiags.clear();
        proofResults.clear();
        // Snapshot markedUris before clearing so we don't modify the set while iterating.
        List<String> toClean = new ArrayList<>(markedUris);
        markedUris.clear();
        for (String uri : toClean) {
            if (client != null) client.publishDiagnostics(new PublishDiagnosticsParams(uri, List.of()));
        }
        //debugContent("after clearMarkers");
        refreshCodeLenses();
    }

    void clearMarkersForUris(List<String> targetUris) {
        ServerLog.serverLog("[clearMarkersForUris] targets=" + targetUris
                + " markedUris=" + markedUris);
        // Build normalized folder prefixes (always end with /).
        List<String> prefixes = new java.util.ArrayList<>();
        for (String t : targetUris) prefixes.add(t.endsWith("/") ? t : t + "/");

        List<String> toClear = new ArrayList<>();
        for (String marked : markedUris) {
            for (int i = 0; i < targetUris.size(); i++) {
                if (marked.equals(targetUris.get(i)) || marked.startsWith(prefixes.get(i))) {
                    toClear.add(marked);
                    break;
                }
            }
        }
        if (toClear.isEmpty()) {
            ServerLog.serverLog("[clearMarkersForUris] no markers found for targets");
        } else {
            ServerLog.serverLog("[clearMarkersForUris] matched=" + toClear);
        }
        for (String uri : toClear) {
            checkDiags.remove(uri);
            String uriPrefix = uri + "#";
            proofResults.keySet().removeIf(k -> k.equals(uri) || k.startsWith(uriPrefix));
            markedUris.remove(uri);
            if (client != null) client.publishDiagnostics(new PublishDiagnosticsParams(uri, List.of()));
        }
        //debugContent("after clearMarkersForUris");
        clientLog("[OpenJML] Cleared selected diagnostics.");
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
        cancelEsc(null, null);  // cancel all futures and abort any live z3 processes
        lastCheckFuture.clear();

        // Clear all diagnostic and status caches.
        checkDiags.clear();
        proofResults.clear();
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
        // Mark all projects dirty so the next nav operation triggers fresh checks.
        projectNavDirty.values().forEach(d -> d.set(true));

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
        initProjectNavState();
        if (globalSettings.projects != null && !globalSettings.projects.isEmpty()) {
            for (ProjectConfig cfg : globalSettings.projects)
                executor.submit(() -> requestNavUpdate(cfg.id));
        } else {
            executor.submit(() -> requestNavUpdate(OpenJMLSettings.WORKSPACE_PROJECT_ID));
        }
    }

    /**
     * Index the source directories of the specified project (or all projects
     * when {@code projectId} is null or empty) by running a {@code --check}
     * pass.  Diagnostics and nav-tier AST cache entries are replaced for every
     * file the check touches; files not reached retain their previous values.
     */
    void indexProject(String projectId) {
        boolean hasProjects = globalSettings.projects != null && !globalSettings.projects.isEmpty();
        boolean projectIdGiven = projectId != null && !projectId.isEmpty();

        if (hasProjects && projectIdGiven) {
            boolean matched = globalSettings.projects.stream()
                    .anyMatch(cfg -> projectId.equals(cfg.id));
            if (!matched) {
                clientError("OpenJML: indexProject — unknown project id '" + projectId + "'.");
                return;
            }
        }

        // Mark dirty and submit a nav update (requestNavUpdate computes roots itself).
        String effectiveId = projectIdGiven ? projectId : null;
        if (effectiveId != null) {
            AtomicBoolean d = projectNavDirty.computeIfAbsent(
                    effectiveId, k -> new AtomicBoolean(true));
            d.set(true);
        } else {
            projectNavDirty.values().forEach(d -> d.set(true));
        }
        executor.submit(() -> requestNavUpdate(effectiveId));
    }

    /** Shut down all executor services. Called from the language server's shutdown sequence. */
    void shutdown() {
        scheduler.shutdownNow();
        executor.shutdownNow();
    }

    /**
     * AST walker that finds the innermost method whose declaration span contains a given
     * 0-based target line.
     *
     * <p>Strategy: recurse only into methods that contain the line.  After the recursive
     * call returns (meaning no nested method claimed the match), the current method is
     * the innermost one — record it and throw {@link Found} to stop the entire scan.
     * If a nested method matches, its {@link Found} propagates through the enclosing
     * method's {@code super} call, so the enclosing method never claims the match.
     */
    private static final class MethodAtLineScanner extends JmlTreeScanner {
        private final JmlCompilationUnit cu;
        private final int targetLine;
        JavaSourceScanner.MethodInfo best = null;

        private static final class Found extends RuntimeException {
            Found() { super(null, null, true, false); }
        }

        MethodAtLineScanner(JmlCompilationUnit cu, int targetLine) {
            super(null);
            this.cu = cu;
            this.targetLine = targetLine;
        }

        void scanForMethod(JmlCompilationUnit ast) {
            try { scan(ast); } catch (Found ignored) {}
        }

        @Override
        public void visitMethodDef(JCMethodDecl tree) {
            if (tree.pos < 0 || tree.sym == null) return;
            String rawName = tree.name != null ? tree.name.toString() : "";
            if (rawName.isEmpty() || (rawName.startsWith("<") && !"<init>".equals(rawName))) return;

            int startLine = Math.max(0, (int) cu.lineMap.getLineNumber(tree.pos) - 1);
            int endOffset = cu.endPositions != null ? tree.getEndPosition(cu.endPositions) : -1;
            int endLine   = (endOffset > tree.pos)
                    ? Math.max(startLine, (int) cu.lineMap.getLineNumber(endOffset) - 1)
                    : startLine;

            ServerLog.serverLog("[MethodAtLineScanner] target=" + targetLine
                    + " method=" + rawName + " start=" + startLine + " end=" + endLine
                    + (targetLine >= startLine && targetLine <= endLine ? " IN-RANGE" : " skip"));

            if (targetLine < startLine || targetLine > endLine) return;

            super.visitMethodDef(tree);  // recurse — if a nested method matches it throws Found

            // No nested method claimed the match — this is the innermost one.
            String ownerSimple = tree.sym.owner != null
                    ? tree.sym.owner.getSimpleName().toString() : "";
            String name = "<init>".equals(rawName)
                    ? (ownerSimple.isEmpty() ? "<init>" : ownerSimple) : rawName;
            String fqnKey = Utils.uniqueSymbolName(tree.sym);
            int bodyStart = (tree.body != null && tree.body.pos > tree.pos)
                    ? Math.max(startLine, (int) cu.lineMap.getLineNumber(tree.body.pos) - 1)
                    : endLine;
            String cuUri = cu.sourcefile != null
                    ? cu.sourcefile.toUri().normalize().toString() : "";
            String sourceUri = (tree instanceof JmlMethodDecl jm && jm.sourcefile != null)
                    ? jm.sourcefile.toUri().normalize().toString() : cuUri;
            best = new JavaSourceScanner.MethodInfo(
                    name, fqnKey, startLine, startLine, bodyStart, endLine, sourceUri);
            throw new Found();
        }
    }
}
