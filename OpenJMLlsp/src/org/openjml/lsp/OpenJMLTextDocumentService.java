package org.openjml.lsp;

import org.eclipse.lsp4j.CodeLens;
import org.eclipse.lsp4j.CodeLensParams;
import org.eclipse.lsp4j.Command;
import org.eclipse.lsp4j.CompletionItem;
import org.eclipse.lsp4j.CompletionList;
import org.eclipse.lsp4j.CompletionParams;
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
import org.eclipse.lsp4j.FoldingRange;
import org.eclipse.lsp4j.FoldingRangeRequestParams;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.jsonrpc.messages.Either3;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.TextDocumentService;
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
                case UNKNOWN      -> "OpenJML: \u2014";                 // —
                case CHECKING     -> "OpenJML: \u29d7 Checking\u2026";  // ⧗
                case VERIFIED     -> "OpenJML: \u2713 Verified";
                case INFEASIBLE   -> "OpenJML: Infeasible";
                case NOT_VERIFIED -> "OpenJML: \u2717 Not verified"     // ✗
                        + (issueCount > 0 ? " (" + issueCount + " issue(s))" : "");
                case SKIPPED      -> "OpenJML: Skipped";
                case TIMEOUT      -> "OpenJML: Timeout";
                case CANCELLED    -> "OpenJML: Cancelled";
                case CHECK_ERROR       -> "OpenJML: Check error";
                case CHECK_ERROR_DEPS  -> "OpenJML: Check error in other files";
            };
        }
    }

    private final OpenJMLSettings settings;
    private final String codeLensCommand;
    private LanguageClient client;

    /** Workspace root URI, stored when the first workspace index is scheduled. */
    private volatile String rootUri = null;

    private final ExecutorService          executor      = Executors.newCachedThreadPool();
    private final ScheduledExecutorService scheduler     = Executors.newSingleThreadScheduledExecutor();

    /**
     * Dedicated single-thread executor for the background workspace index.
     * Kept separate from {@code executor} so the potentially long-running index
     * pass never blocks user-triggered check/ESC requests.
     * The thread is a daemon so it does not prevent JVM exit.
     */
    private final ExecutorService indexExecutor = Executors.newSingleThreadExecutor(r -> {
        Thread t = new Thread(r, "openjml-index");
        t.setDaemon(true);
        return t;
    });

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

    /** Per-method ESC status, keyed by URI then method start line. */
    private final Map<String, Map<Integer, MethodStatus>> methodEscStatus = new ConcurrentHashMap<>();

    /** Last-seen source content per URI (for code lens and hover). */
    private final Map<String, String> lastContent = new ConcurrentHashMap<>();

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
     * @param settings        shared settings object
     * @param codeLensCommand the command name to embed in code-lens actions (e.g. run ESC for method)
     */
    public OpenJMLTextDocumentService(OpenJMLSettings settings, String codeLensCommand) {
        this.settings       = settings;
        this.codeLensCommand = codeLensCommand;
    }

    public void connect(LanguageClient client) {
        this.client = client;
        CheckRunner.setLogCallback(msg -> {
            if (client != null)
                client.logMessage(new MessageParams(MessageType.Log, msg));
        });
    }

    @Override
    public void didOpen(DidOpenTextDocumentParams params) {
        String uri     = params.getTextDocument().getUri();
        String content = params.getTextDocument().getText();
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
        String content = params.getContentChanges().get(0).getText();
        lastContent.put(uri, content);
        // Invalidate cached check state for all other open files so that focus-triggered
        // rechecks pick up this change in their cross-file context.  When the primary
        // check completes, companion files that were actually compiled will be re-marked
        // as up-to-date, so only truly-uncompiled files will be rechecked on focus.
        lastCheckedContent.keySet().removeIf(k -> !k.equals(uri));

        // --check: debounced if in edit mode
        if (settings.isCheckOnEdit()) {
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
        if (settings.isEscOnEdit()) {
            debounce(pendingEsc, uri,
                    () -> startEscContent(uri, content),
                    ESC_DEBOUNCE_MS);
        }
    }

    @Override
    public void didSave(DidSaveTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
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
            String fqn = JavaSourceScanner.methodFqn(content, m.name());
            var cmd = new Command(s.label(), codeLensCommand,
                                  List.<Object>of(uri, fqn));
            lenses.add(new CodeLens(range, cmd, null));
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
        boolean jmlOnly = !Boolean.TRUE.equals(settings.useIntegratedOutline);
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
        System.err.println("[hover] uri=" + uri);
        String content = lastContent.get(uri);
        if (content == null) return CompletableFuture.completedFuture(null);

        int line = params.getPosition().getLine();
        List<JavaSourceScanner.MethodInfo> methods = JavaSourceScanner.findMethods(content);

        // Find the innermost method containing the cursor line.
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
        ASTCache cache = CheckRunner.getASTCache();
        boolean hasAst = cache.get(uri) != null;
        System.err.println("[OpenJML] definition: uri=" + uri
                + "  hasContent=" + (source != null)
                + "  hasAST=" + hasAst);
        if (source == null)
            return CompletableFuture.completedFuture(Either.forLeft(List.of()));

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
                return ready.thenApply(v -> {
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

        ASTCache cache = CheckRunner.getASTCache();
        if (uri.endsWith(".jml") && cache.get(uri) == null) {
            String javaUri = resolveCompanionJavaUri(uri, source);
            if (javaUri != null) {
                String jmlSource = source;
                CompletableFuture<Void> pending = lastCheckFuture.get(javaUri);
                CompletableFuture<Void> ready = (pending != null && !pending.isDone())
                        ? pending : CompletableFuture.completedFuture(null);
                return ready.thenApply(v -> {
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
     */
    @Override
    public CompletableFuture<WorkspaceEdit> rename(RenameParams params) {
        String uri = params.getTextDocument().getUri();
        if (lastContent.get(uri) == null)
            return CompletableFuture.completedFuture(null);

        return ensureFreshAndConfirm(uri, "Rename").thenCompose(proceed -> {
            if (!proceed) return CompletableFuture.completedFuture(null);
            try {
                WorkspaceEdit edit = Renamer.rename(
                        uri,
                        params.getPosition().getLine(),
                        params.getPosition().getCharacter(),
                        params.getNewName(),
                        lastContent,
                        CheckRunner.getASTCache(),
                        settings);
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
    void scheduleCheckForPaths(List<String> paths, String sourcePath, String classPath,
                                String specsPath, String propertiesFile) {
        if (paths == null || paths.isEmpty()) return;
        OpenJMLSettings s = withContext(sourcePath, classPath, specsPath, propertiesFile, null);
        List<String> pathsCopy = List.copyOf(paths);

        // Snapshot dirty-file content at submission time so rapid edits during the
        // debounce window do not mutate the context passed to OpenJML.
        Map<String, String> snapshot = Map.copyOf(lastContent);

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
                        checkDiags.put(entry.getKey(), entry.getValue());
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
    void scheduleEscForPaths(List<String> paths, String sourcePath, String classPath,
                              String specsPath, String propertiesFile) {
        if (paths == null || paths.isEmpty()) return;
        OpenJMLSettings s = withContext(sourcePath, classPath, specsPath, propertiesFile, null);

        // Mark all directly-specified open files as CHECKING before submitting.
        // Directory paths are handled after the run via the affected-URI scan.
        for (String path : paths) {
            try {
                java.nio.file.Path p = java.nio.file.Path.of(path);
                if (!java.nio.file.Files.isDirectory(p)) {
                    String uri = p.toUri().toString();
                    if (lastContent.containsKey(uri)) markAllMethodStatus(uri, MethodStatus.CHECKING);
                }
            } catch (Exception ignored) {}
        }
        refreshCodeLenses();

        // Snapshot dirty-file content before submitting so edits during the run
        // do not mutate the context map passed to OpenJML.
        Map<String, String> escSnapshot = Map.copyOf(lastContent);

        executor.submit(() -> {
            try {
                // Publish ESC diagnostics progressively as each method's proof completes.
                // Skip publishing when diags is empty: the callback fires after each method's
                // proof result, but the diagnostic for a failed proof may not yet be in the
                // listener's collected list at that instant.  Publishing empty mid-run would
                // prematurely clear any previously-shown diagnostics; the post-run loop below
                // handles the final state for all files including fully-verified ones.
                CheckRunner.DirCheckResult result = CheckRunner.runEscDirWithContext(paths, escSnapshot, s, (uri, diags) -> {
                    if (client == null || diags.isEmpty()) return;
                    escDiags.put(uri, diags);
                    publishMerged(uri);
                });
                if (client == null) return;
                // After the full run, publish the final state for every affected file
                // (catches any remaining diagnostics not yet covered by the callback).
                for (var entry : result.diagnosticsByUri().entrySet()) {
                    escDiags.put(entry.getKey(), entry.getValue());
                    publishMerged(entry.getKey());
                }
                // Clear ESC diagnostics for files that had none but are currently open.
                for (String path : paths) {
                    String uri;
                    try { uri = java.nio.file.Path.of(path).toUri().toString(); }
                    catch (Exception e) { continue; }
                    if (!result.diagnosticsByUri().containsKey(uri) && lastContent.containsKey(uri)) {
                        escDiags.remove(uri);
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
                    }
                }
            } catch (Throwable e) {
                System.err.println("[scheduleEscForPaths] error: " + e.getMessage());
            }
        });
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
    void scheduleRacForPaths(List<String> paths, String sourcePath, String classPath,
                              String specsPath, String propertiesFile, String outputDir) {
        if (paths == null || paths.isEmpty()) return;
        OpenJMLSettings s = withContext(sourcePath, classPath, specsPath, propertiesFile, outputDir);
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
        if (!settings.isRegexColoring() && !uri.endsWith(".jml")) {
            ASTCache.Entry entry = CheckRunner.getASTCache().get(uri);
            if (entry != null) {
                System.err.println("[getSemanticTokens] strategy=AST uri=" + uri);
                return SemanticTokensProvider.computeTokensFromAst(entry, content).getData();
            }
        }
        System.err.println("[getSemanticTokens] strategy=regex uri=" + uri);
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
            System.err.println("[semanticTokensFull] uri=" + uri + " tokens=" + data.size() / 5);
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
    List<SymbolInformation> symbols(String query) {
        if (CheckRunner.getASTCache().isIndexing()) {
            clientLog("workspace/symbol: background index still running — results may be incomplete");
        }
        String lowerQuery = query == null ? "" : query.toLowerCase(java.util.Locale.ROOT);
        List<SymbolInformation> result = new ArrayList<>();
        CheckRunner.getASTCache().forEachDeclaration((sym, loc) -> {
            String name = sym.name.toString();
            // Skip synthetic names (<init>, <clinit>, empty).
            if (name.isEmpty() || name.startsWith("<")) return;
            // Filter by query (case-insensitive substring match; empty = accept all).
            if (!lowerQuery.isEmpty()
                    && !name.toLowerCase(java.util.Locale.ROOT).contains(lowerQuery)) return;
            // Offset → Position requires source content.
            // Prefer in-memory content (for unsaved edits); fall back to disk.
            String content = lastContent.get(loc.uri());
            if (content == null) {
                String path = CheckRunner.uriToPath(loc.uri());
                if (path != null) {
                    try { content = java.nio.file.Files.readString(java.nio.file.Path.of(path)); }
                    catch (java.io.IOException ignored) {}
                }
            }
            if (content == null) return;
            Position pos = offsetToPosition(content, loc.charOffset());
            var location = new Location(loc.uri(), new Range(pos, pos));
            result.add(new SymbolInformation(name, symbolKind(sym), location));
        });
        return result;
    }

    /**
     * Schedule a background workspace index pass on all {@code .java} files
     * under {@code rootUri}.  Called once after the LSP {@code initialized}
     * handshake so that {@code workspace/symbol} can find symbols in files
     * that have not been opened by the user.
     *
     * <p>Runs on a dedicated daemon thread ({@code indexExecutor}) so it never
     * blocks user-triggered check or ESC requests.  Files are checked one at a
     * time; diagnostics are published incrementally after each file so the user
     * sees results as they arrive.  Files already open in the editor are skipped
     * (their live check takes priority).
     *
     * @param rootUri the workspace root URI from {@code InitializeParams}
     */
    void scheduleWorkspaceIndex(String rootUri) {
        this.rootUri = rootUri;
        String rootPath = CheckRunner.uriToPath(rootUri);
        if (rootPath == null) return;
        indexExecutor.submit(() -> {
            try {
                List<String> filePaths;
                try (var stream = java.nio.file.Files.walk(java.nio.file.Path.of(rootPath))) {
                    filePaths = stream
                            .filter(p -> { String s = p.toString(); return s.endsWith(".java") || s.endsWith(".jml"); })
                            .map(java.nio.file.Path::toString)
                            .collect(java.util.stream.Collectors.toList());
                }
                if (filePaths.isEmpty()) return;

                CheckRunner.getASTCache().setIndexing(true);
                clientLog("OpenJML: indexing workspace (" + filePaths.size() + " file(s))…");

                int indexed = 0, totalDiags = 0;
                try {
                    for (String filePath : filePaths) {
                        String uri = java.nio.file.Path.of(filePath).toUri().toString();
                        // Skip files the user already has open — their live check takes priority.
                        if (lastContent.containsKey(uri)) continue;

                        List<Diagnostic> diags = CheckRunner.indexOneFile(filePath, uri, settings);
                        indexed++;
                        if (!diags.isEmpty()) {
                            totalDiags += diags.size();
                            checkDiags.put(uri, diags);
                            publishMerged(uri);
                        }
                        // Log progress every 50 files for large workspaces.
                        if (indexed % 50 == 0 && client != null) {
                            client.logMessage(new MessageParams(MessageType.Log,
                                    "OpenJML: indexed " + indexed + " / " + filePaths.size() + " file(s)…"));
                        }
                    }
                } finally {
                    CheckRunner.getASTCache().setIndexing(false);
                    clientLog("OpenJML: workspace index complete — "
                            + indexed + " file(s), " + totalDiags + " diagnostic(s)");
                }
            } catch (Throwable e) {
                System.err.println("[OpenJML] Background index failed: " + e);
                CheckRunner.getASTCache().setIndexing(false);
            }
        });
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
     * Returns a per-invocation copy of {@link #settings} with path/settings fields
     * overridden by any non-empty arguments, or {@code settings} itself when all
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
        if (!hasSrc && !hasCp && !hasSp && !hasPf && !hasOd) return settings;
        OpenJMLSettings s = new OpenJMLSettings(settings);
        if (hasSrc) s.sourcePath              = sourcePath;
        if (hasCp)  s.classPath               = classPath;
        if (hasSp)  s.specsPath               = specsPath;
        if (hasPf)  s.generatedPropertiesFile  = propertiesFile;
        if (hasOd)  s.racOutputDir             = outputDir;
        return s;
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
    void scheduleCheckForUri(String uri, String sourcePath, String classPath,
                             String specsPath, String propertiesFile) {
        OpenJMLSettings s = withContext(sourcePath, classPath, specsPath, propertiesFile, null);
        String content = lastContent.get(uri);
        if (content != null) {
            // File is open — check the current in-memory content.
            executor.submit(() -> runCheckContent(uri, content, s));
        } else {
            // File is not open — check from disk.
            String filePath = CheckRunner.uriToPath(uri);
            if (filePath == null) return;
            executor.submit(() -> {
                try {
                    CheckRunner.CheckResult result = CheckRunner.checkFile(filePath, uri, s);
                    checkDiags.put(uri, result.diagnostics());
                    publishMerged(uri);
                } catch (Throwable e) {
                    System.err.println("[OpenJML] checkForUri failed: " + e);
                }
            });
        }
    }

    /**
     * Trigger a --check recheck of an already-open file (e.g. when focus returns
     * to it after its dependencies were edited).  Uses in-memory content so that
     * unsaved edits are included.  No-op if the file is not currently open.
     */
    void recheckUri(String uri) {
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

    void scheduleEscForUri(String uri, String sourcePath, String classPath,
                           String specsPath, String propertiesFile) {
        OpenJMLSettings s = withContext(sourcePath, classPath, specsPath, propertiesFile, null);
        if (s.isEscApiMode()) {
            submitEscApiWorkList(uri, s);
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
        submitEscApiWorkList(uri, settings);
    }

    private void submitEscApiWorkList(String uri, OpenJMLSettings s) {
        Future<?> prev = runningEscTasks.remove(uri);
        if (prev != null) prev.cancel(true);

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
            escDiags.put(uri, result.diagnostics());
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
    void scheduleEscForMethod(String uri, String methodName, String sourcePath, String classPath,
                              String specsPath, String propertiesFile) {
        OpenJMLSettings s = withContext(sourcePath, classPath, specsPath, propertiesFile, null);
        String content = lastContent.get(uri);
        JavaSourceScanner.MethodInfo target = findMethodByFqn(content, methodName);

        if (s.isEscApiMode()) {
            // Submit through escPool so this request joins the same shared queue
            // as any in-flight runDoEscFileAsync tasks for the same URI.
            submitEscForMethod(uri, target,
                    () -> CheckRunner.runDoEscMethod(uri, methodName, s),
                    s.escPool);
        } else {
            String contentForMethod = lastContent.get(uri);
            Map<String, String> snapshot = Map.copyOf(lastContent);
            if (contentForMethod != null) {
                final String c = contentForMethod;
                submitEscForMethod(uri, target,
                        () -> CheckRunner.escMethodWithContext(uri, c, methodName, snapshot, s),
                        executor);
            } else {
                String filePath = CheckRunner.uriToPath(uri);
                if (filePath != null)
                    submitEscForMethod(uri, target,
                            () -> CheckRunner.runEscFileMethod(filePath, uri, methodName, s),
                            executor);
            }
        }
    }

    /**
     * Extract the simple name from a possibly-qualified method name
     * ({@code "pkg.Class.method"} → {@code "method"}) and find the matching
     * {@link JavaSourceScanner.MethodInfo} in {@code content}.
     * Returns {@code null} if the content is absent or no match is found.
     */
    private static JavaSourceScanner.MethodInfo findMethodByFqn(String content, String fqn) {
        if (content == null || fqn == null) return null;
        int dot = fqn.lastIndexOf('.');
        String simpleName = dot >= 0 ? fqn.substring(dot + 1) : fqn;
        for (JavaSourceScanner.MethodInfo m : JavaSourceScanner.findMethods(content)) {
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
                                    Supplier<CheckRunner.CheckResult> task,
                                    ExecutorService pool) {
        Future<?> prev = runningEscTasks.remove(uri);
        if (prev != null) prev.cancel(true);

        long myGen = escGen.computeIfAbsent(uri, k -> new AtomicLong()).incrementAndGet();

        // Mark only the target method as CHECKING.
        if (target != null) {
            Map<Integer, MethodStatus> statuses =
                    new java.util.HashMap<>(methodEscStatus.getOrDefault(uri, Map.of()));
            statuses.put(target.startLine(), MethodStatus.CHECKING);
            methodEscStatus.put(uri, statuses);
            refreshCodeLenses();
        } else {
            markEscChecking(uri);
        }

        Future<?> f = pool.submit(() -> {
            try {
                CheckRunner.CheckResult result = task.get();
                if (result.isCommandLineError())
                    System.err.println("[OpenJML] BUG: exit code 2 (bad command-line args) from ESC-method for " + uri);
                if (escGen.get(uri).get() != myGen) return; // superseded

                if (result.isInternalError()) {
                    System.err.println("[OpenJML] ESC for method: internal error (exit code " + result.exitCode() + ")");
                    escDiags.put(uri, result.diagnostics());
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
                    escDiags.put(uri, kept);

                    // Update only the target method's code-lens status using
                    // the proof result if available, else fall back to diag count.
                    String simpleName = target.name();
                    IProverResult.Kind kind = result.proofResults().get(simpleName);
                    MethodStatus ms = proofResultToStatus(kind, diags, start, end,
                                                          result.exitCode(), result.hasForeignErrors());
                    Map<Integer, MethodStatus> statuses =
                            new java.util.HashMap<>(methodEscStatus.getOrDefault(uri, Map.of()));
                    statuses.put(start, ms);
                    methodEscStatus.put(uri, statuses);
                } else {
                    escDiags.put(uri, diags);
                    updateEscStatus(uri, diags, result.proofResults(), result.exitCode(),
                                        result.foreignMessages());
                }
                publishMerged(uri);
                refreshCodeLenses();
            } catch (Throwable t) {
                System.err.println("[OpenJML] ESC for method failed unexpectedly: " + t);
                if (target != null && escGen.get(uri).get() == myGen) {
                    Map<Integer, MethodStatus> statuses =
                            new java.util.HashMap<>(methodEscStatus.getOrDefault(uri, Map.of()));
                    statuses.put(target.startLine(), MethodStatus.UNKNOWN);
                    methodEscStatus.put(uri, statuses);
                    refreshCodeLenses();
                }
            } finally {
                runningEscTasks.remove(uri);
            }
        });
        runningEscTasks.put(uri, f);
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
     *       enum/record name.  Then search each root in {@code workspaceFolderPaths} and
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
        List<String> roots = new ArrayList<>();
        if (settings.workspaceFolderPaths != null && !settings.workspaceFolderPaths.isEmpty())
            java.util.Collections.addAll(roots,
                    settings.workspaceFolderPaths.split(java.io.File.pathSeparator));
        if (settings.sourcePath != null && !settings.sourcePath.isEmpty())
            java.util.Collections.addAll(roots,
                    settings.sourcePath.split(java.io.File.pathSeparator));
        for (String root : roots) {
            java.nio.file.Path candidate = java.nio.file.Path.of(root).resolve(relPath);
            if (java.nio.file.Files.isRegularFile(candidate))
                return candidate.toUri().toString();
        }
        return null;
    }

    private void scheduleCheckNow(String uri, String content) {
        // .jml files are spec files; redirect check to companion .java
        if (uri.endsWith(".jml")) {
            String javaUri = resolveCompanionJavaUri(uri, content);
            if (javaUri == null) return;
            String javaContent = lastContent.get(javaUri);
            if (javaContent != null) {
                CompletableFuture<Void> cf = new CompletableFuture<>();
                lastCheckFuture.put(javaUri, cf);
                executor.submit(() -> { try { runCheckContent(javaUri, javaContent); } finally { cf.complete(null); } });
            } else {
                String filePath = CheckRunner.uriToPath(javaUri);
                if (filePath != null && new java.io.File(filePath).exists()) {
                    CompletableFuture<Void> cf = new CompletableFuture<>();
                    lastCheckFuture.put(javaUri, cf);
                    executor.submit(() -> { try { runCheckFile(filePath, javaUri); } finally { cf.complete(null); } });
                }
            }
            return;
        }
        String filePath = CheckRunner.uriToPath(uri);
        CompletableFuture<Void> cf = new CompletableFuture<>();
        lastCheckFuture.put(uri, cf);
        if (filePath != null && new java.io.File(filePath).exists()) {
            executor.submit(() -> { try { runCheckFile(filePath, uri); } finally { cf.complete(null); } });
        } else {
            executor.submit(() -> { try { runCheckContent(uri, content); } finally { cf.complete(null); } });
        }
    }

    private void scheduleCheckFile(String uri) {
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
        // For .java files: prefer content-based check if the file is open in memory,
        // so that the current (possibly unsaved) .jml companion content is also checked.
        runWithContentOrFile(uri,
                c -> executor.submit(() -> runCheckContent(uri, c)),
                f -> executor.submit(() -> runCheckFile(f, uri)));
    }

    private void scheduleEscFile(String uri) {
        String content = lastContent.get(uri);
        if (content != null) {
            Map<String, String> snapshot = Map.copyOf(lastContent);
            submitEsc(uri, () -> CheckRunner.escWithContext(uri, content, snapshot, settings));
        } else {
            String filePath = CheckRunner.uriToPath(uri);
            if (filePath != null) submitEsc(uri, () -> CheckRunner.runEscFile(filePath, uri, settings));
        }
    }

    /**
     * If {@code uri} has in-memory content (i.e. the file is open in an editor),
     * invoke {@code onContent} with that content; otherwise resolve the on-disk
     * path and invoke {@code onFile} with it.  Silently returns if neither source
     * is available (file path cannot be determined).
     *
     * <p>Both {@link #scheduleCheckFile} and {@link #scheduleEscFile} apply the
     * same "prefer edited content over saved file" policy — this helper avoids
     * duplicating that logic.
     */
    private void runWithContentOrFile(String uri,
            java.util.function.Consumer<String> onContent,
            java.util.function.Consumer<String> onFile) {
        String content = lastContent.get(uri);
        if (content != null) { onContent.accept(content); return; }
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath == null) return;
        onFile.accept(filePath);
    }

    private void scheduleEscFile(String uri, OpenJMLSettings s) {
        String content = lastContent.get(uri);
        if (content != null) {
            Map<String, String> snapshot = Map.copyOf(lastContent);
            submitEsc(uri, () -> CheckRunner.escWithContext(uri, content, snapshot, s));
            return;
        }
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath == null) return;
        submitEsc(uri, () -> CheckRunner.runEscFile(filePath, uri, s));
    }


    private void startEscContent(String uri, String content) {
        Map<String, String> snapshot = Map.copyOf(lastContent);
        submitEsc(uri, () -> CheckRunner.escWithContext(uri, content, snapshot, settings));
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
    private void submitEsc(String uri, Supplier<CheckRunner.CheckResult> task) {
        // Cancel the previous ESC task for this URI (may not interrupt CPU-bound work,
        // but removes it from the task queue if it hasn't started yet).
        Future<?> prev = runningEscTasks.remove(uri);
        if (prev != null) prev.cancel(true);

        long myGen = escGen.computeIfAbsent(uri, k -> new AtomicLong()).incrementAndGet();
        markEscChecking(uri);

        Future<?> f = executor.submit(() -> {
            try {
                CheckRunner.CheckResult result = task.get();
                if (result.isCommandLineError())
                    System.err.println("[OpenJML] BUG: exit code 2 (bad command-line args) from ESC for " + uri);
                // Only publish if this task is still the latest for this URI.
                if (escGen.get(uri).get() == myGen) {
                    escDiags.put(uri, result.diagnostics());
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
        if (isWorkspaceStale()) {
            String content = lastContent.get(primaryUri);
            if (content == null)
                return CompletableFuture.completedFuture(false);
            checkFuture = CompletableFuture.runAsync(
                    () -> runCheckContent(primaryUri, content), executor);
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
        runCheckContent(uri, content, settings);
    }

    private void runCheckContent(String uri, String content, OpenJMLSettings s) {
        // .jml files are spec files; should not be passed to OpenJML on command line.
        // scheduleCheckNow redirects to the companion .java, but guard here as well.
        if (uri.endsWith(".jml")) return;
        lastCheckedContent.put(uri, content);
        try {
            // Snapshot lastContent at execution time so that concurrent edits do not
            // mutate the context map while OpenJML is parsing it.
            Map<String, String> snapshot = Map.copyOf(lastContent);
            CheckRunner.CheckResult result = CheckRunner.checkWithContext(
                    uri, content, snapshot, s);
            // Publish diagnostics for all compiled files (primary + companions) uniformly.
            result.allDiagnostics().forEach((diagUri, diags) -> {
                checkDiags.put(diagUri, diags);
                publishMerged(diagUri);
                String c = lastContent.get(diagUri);
                if (c != null) lastCheckedContent.put(diagUri, c);
            });
            // If allDiagnostics is empty (non-context check), fall back to primary.
            if (result.allDiagnostics().isEmpty()) {
                checkDiags.put(uri, result.diagnostics());
                publishMerged(uri);
            }
            // Do NOT call refreshCodeLenses() here.
        } catch (Throwable t) {
            System.err.println("[OpenJML] check failed for " + uri + ": " + t);
        }
    }

    private void runCheckFile(String filePath, String uri) {
        try {
            CheckRunner.CheckResult result = CheckRunner.checkFile(filePath, uri, settings);
            checkDiags.put(uri, result.diagnostics());
            publishMerged(uri);
            // runOnFile does not use the context path so no companion diagnostics.
            // Do NOT call refreshCodeLenses() here.
        } catch (Throwable t) {
            System.err.println("[OpenJML] check file failed for " + uri + ": " + t);
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
        List<JavaSourceScanner.MethodInfo> methods = JavaSourceScanner.findMethods(content);
        if (methods.isEmpty()) return;

        boolean hasForeignErrors = !foreignFiles.isEmpty();
        Map<Integer, MethodStatus> statuses = new HashMap<>();
        for (JavaSourceScanner.MethodInfo m : methods) {
            IProverResult.Kind kind = proofResults.get(m.name());
            statuses.put(m.startLine(),
                    proofResultToStatus(kind, diags, m.startLine(), m.endLine(),
                                        exitCode, hasForeignErrors));
        }
        methodEscStatus.put(uri, statuses);
        refreshCodeLenses();

        if (hasForeignErrors) {
            String fileName = uri.substring(uri.lastIndexOf('/') + 1);
            clientWarn("OpenJML: ESC on " + fileName
                    + " could not run — type errors in: " + String.join(", ", foreignFiles));
        }
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
     * Clear all in-memory caches and restart as if the server had just started.
     *
     * <p>Cancels any pending check/ESC work, clears the AST cache, diagnostic
     * maps, and ESC status, publishes empty diagnostics for all open files,
     * then re-queues a fresh {@code --check} for every open file and a fresh
     * workspace index pass.
     *
     * <p>Intended as a recovery command when the user suspects the server state
     * has become stale or is consuming too much memory.
     */
    void resetAndReindex() {
        // Cancel all pending debounced and running work.
        pendingCheck.values().forEach(f -> f.cancel(false));
        pendingCheck.clear();
        pendingEsc.values().forEach(f -> f.cancel(false));
        pendingEsc.clear();
        ScheduledFuture<?> pcp = pendingCheckPaths;
        if (pcp != null) { pcp.cancel(false); pendingCheckPaths = null; }
        runningEscTasks.values().forEach(f -> f.cancel(false));
        runningEscTasks.clear();
        lastCheckFuture.clear();

        // Clear all diagnostic and status caches.
        checkDiags.clear();
        escDiags.clear();
        racDiags.clear();
        methodEscStatus.clear();
        lastCheckedContent.clear();

        // Clear the AST cache (both tiers and declaration indexes).
        CheckRunner.getASTCache().clear();

        // Publish empty diagnostics for all marked URIs so stale markers disappear.
        List<String> toClean = new ArrayList<>(markedUris);
        markedUris.clear();
        for (String uri : toClean) {
            publishDiags(uri, List.of());
        }
        clientLog("OpenJML: caches cleared — re-checking open files and re-indexing workspace…");

        // Re-check every currently open file.
        for (Map.Entry<String, String> e : lastContent.entrySet()) {
            scheduleCheckNow(e.getKey(), e.getValue());
        }

        // Re-run the workspace index if a root was known.
        if (rootUri != null) scheduleWorkspaceIndex(rootUri);

        refreshCodeLenses();
    }

    /** Shut down all executor services. Called from the language server's shutdown sequence. */
    void shutdown() {
        scheduler.shutdownNow();
        executor.shutdownNow();
        indexExecutor.shutdownNow();
    }
}
