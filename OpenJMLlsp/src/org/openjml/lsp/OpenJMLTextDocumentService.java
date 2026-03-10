package org.openjml.lsp;

import org.eclipse.lsp4j.CodeLens;
import org.eclipse.lsp4j.CodeLensParams;
import org.eclipse.lsp4j.Command;
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
import org.eclipse.lsp4j.MessageParams;
import org.eclipse.lsp4j.MessageType;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.PrepareRenameDefaultBehavior;
import org.eclipse.lsp4j.PrepareRenameParams;
import org.eclipse.lsp4j.PrepareRenameResult;
import org.eclipse.lsp4j.PublishDiagnosticsParams;
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

    enum EscPhase { UNKNOWN, CHECKING, VERIFIED, INFEASIBLE, NOT_VERIFIED, SKIPPED, TIMEOUT, CANCELLED, CHECK_ERROR, CHECK_ERROR_DEPS }

    record MethodStatus(EscPhase phase, int issueCount) {
        static final MethodStatus UNKNOWN      = new MethodStatus(EscPhase.UNKNOWN,      0);
        static final MethodStatus CHECKING     = new MethodStatus(EscPhase.CHECKING,     0);
        static final MethodStatus VERIFIED     = new MethodStatus(EscPhase.VERIFIED,     0);
        static final MethodStatus INFEASIBLE   = new MethodStatus(EscPhase.INFEASIBLE,   0);
        static final MethodStatus SKIPPED      = new MethodStatus(EscPhase.SKIPPED,      0);
        static final MethodStatus TIMEOUT      = new MethodStatus(EscPhase.TIMEOUT,      0);
        static final MethodStatus CANCELLED    = new MethodStatus(EscPhase.CANCELLED,    0);
        static final MethodStatus CHECK_ERROR       = new MethodStatus(EscPhase.CHECK_ERROR,       0);
        static final MethodStatus CHECK_ERROR_DEPS  = new MethodStatus(EscPhase.CHECK_ERROR_DEPS,  0);
        static MethodStatus notVerified(int n) { return new MethodStatus(EscPhase.NOT_VERIFIED, n); }
        static MethodStatus done(int n) {
            return n == 0 ? VERIFIED : notVerified(n);
        }

        String label() {
            return switch (phase) {
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

    private final ExecutorService          executor  = Executors.newCachedThreadPool();
    private final ScheduledExecutorService scheduler = Executors.newSingleThreadScheduledExecutor();

    /** Pending debounce futures for --check, keyed by URI. */
    private final Map<String, ScheduledFuture<?>> pendingCheck = new ConcurrentHashMap<>();

    /** Pending debounce futures for --esc, keyed by URI. */
    private final Map<String, ScheduledFuture<?>> pendingEsc   = new ConcurrentHashMap<>();

    /** Latest --check diagnostics per URI. */
    private final Map<String, List<Diagnostic>> checkDiags = new ConcurrentHashMap<>();

    /** Latest --esc diagnostics per URI. */
    private final Map<String, List<Diagnostic>> escDiags   = new ConcurrentHashMap<>();

    /** Per-URI generation counter: incremented on each new ESC submission. */
    private final Map<String, AtomicLong> escGen = new ConcurrentHashMap<>();

    /** Currently running ESC Future per URI (for cancellation). */
    private final Map<String, Future<?>> runningEscTasks = new ConcurrentHashMap<>();

    /** Per-method ESC status, keyed by URI then method start line. */
    private final Map<String, Map<Integer, MethodStatus>> methodEscStatus = new ConcurrentHashMap<>();

    /** Last-seen source content per URI (for code lens and hover). */
    private final Map<String, String> lastContent = new ConcurrentHashMap<>();

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
    }

    @Override
    public void didOpen(DidOpenTextDocumentParams params) {
        String uri     = params.getTextDocument().getUri();
        String content = params.getTextDocument().getText();
        lastContent.put(uri, content);

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

        // --check: debounced if in edit mode
        if (settings.isCheckOnEdit()) {
            debounce(pendingCheck, uri,
                    () -> runCheckContent(uri, content),
                    CHECK_DEBOUNCE_MS);
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
        lastContent.remove(uri);
        methodEscStatus.remove(uri);
        CheckRunner.getASTCache().remove(uri);
        client.publishDiagnostics(new PublishDiagnosticsParams(uri, List.of()));
    }

    // --- code lens ---

    @Override
    public CompletableFuture<List<? extends CodeLens>> codeLens(CodeLensParams params) {
        String uri = params.getTextDocument().getUri();
        String content = lastContent.get(uri);
        if (content == null) return CompletableFuture.completedFuture(List.of());

        List<JavaSourceScanner.MethodInfo> methods = JavaSourceScanner.findMethods(content);
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
    public CompletableFuture<Hover> hover(HoverParams params) {
        String uri = params.getTextDocument().getUri();
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
        if (source == null)
            return CompletableFuture.completedFuture(Either.forLeft(List.of()));

        Location loc = DefinitionFinder.findDefinition(
                uri,
                params.getPosition().getLine(),
                params.getPosition().getCharacter(),
                lastContent,
                CheckRunner.getASTCache());

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
        String source = lastContent.get(uri);
        if (source == null)
            return CompletableFuture.completedFuture(List.of());

        boolean includeDecl = params.getContext() != null
                && params.getContext().isIncludeDeclaration();

        List<? extends Location> refs = ReferenceFinder.findReferences(
                uri,
                params.getPosition().getLine(),
                params.getPosition().getCharacter(),
                lastContent,
                CheckRunner.getASTCache(),
                includeDecl);

        return CompletableFuture.completedFuture(refs);
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

        Location loc = DefinitionFinder.findDefinition(
                uri,
                params.getPosition().getLine(),
                params.getPosition().getCharacter(),
                lastContent,
                CheckRunner.getASTCache());

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
        String source = lastContent.get(uri);
        if (source == null)
            return CompletableFuture.completedFuture(null);
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
     * Run ESC on the given URI immediately (for the {@code openjml.runEsc} command).
     * Uses the file on disk; if the file does not exist the call is a no-op.
     */
    /**
     * Trigger a --check recheck of an already-open file (e.g. when focus returns
     * to it after its dependencies were edited).  Uses in-memory content so that
     * unsaved edits are included.  No-op if the file is not currently open.
     */
    void recheckUri(String uri) {
        String content = lastContent.get(uri);
        if (content == null) return;
        executor.submit(() -> runCheckContent(uri, content));
    }

    void scheduleEscForUri(String uri) {
        scheduleEscFile(uri);
    }

    /**
     * Run ESC on a single method in the given URI (for the {@code openjml.runEscForMethod}
     * command).  {@code methodName} is the fully-qualified name passed to {@code --method}.
     *
     * <p>Unlike a full-file ESC, only the target method's code-lens status and its
     * diagnostics (within its line range) are updated; other methods are left unchanged.
     */
    void scheduleEscForMethod(String uri, String methodName) {
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath == null) return;

        // Resolve the method's line range now (on the calling thread) so we can
        // do per-method status updates after the task completes.
        String content = lastContent.get(uri);
        JavaSourceScanner.MethodInfo target = findMethodByFqn(content, methodName);

        submitEscForMethod(uri, target,
                () -> CheckRunner.runEscFileMethod(filePath, uri, methodName, settings));
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
                                    Supplier<CheckRunner.CheckResult> task) {
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

        Future<?> f = executor.submit(() -> {
            try {
                CheckRunner.CheckResult result = task.get();
                System.err.println("[OpenJML] ESC-method done: exit=" + result.exitCode()
                        + " diags=" + result.diagnostics().size() + " uri=" + uri);
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

    private void scheduleCheckNow(String uri, String content) {
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath != null && new java.io.File(filePath).exists()) {
            scheduleCheckFile(uri);
        } else {
            executor.submit(() -> runCheckContent(uri, content));
        }
    }

    private void scheduleCheckFile(String uri) {
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath == null) return;
        executor.submit(() -> runCheckFile(filePath, uri));
    }

    private void scheduleEscFile(String uri) {
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath == null) return;
        submitEsc(uri, () -> CheckRunner.runEscFile(filePath, uri, settings));
    }

    private void startEscContent(String uri, String content) {
        submitEsc(uri, () -> CheckRunner.runEsc(uri, content, settings));
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
                System.err.println("[OpenJML] ESC done: exit=" + result.exitCode()
                        + " diags=" + result.diagnostics().size() + " uri=" + uri);
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

    private void runCheckContent(String uri, String content) {
        // Pass all open (possibly unsaved) files so cross-file dependencies use
        // their current in-memory versions rather than the on-disk saved versions.
        CheckRunner.CheckResult result = CheckRunner.checkWithContext(
                uri, content, lastContent, settings);
        checkDiags.put(uri, result.diagnostics());
        publishMerged(uri);
        // Update diagnostics for all dependency files that were actually attributed
        // during this compilation run (the compiler's own AST list, not O(n) re-checks).
        result.companionDiagnostics().forEach((otherUri, diags) -> {
            if (lastContent.containsKey(otherUri)) {
                checkDiags.put(otherUri, diags);
                publishMerged(otherUri);
            }
        });
        // Do NOT call refreshCodeLenses() here.
    }

    private void runCheckFile(String filePath, String uri) {
        CheckRunner.CheckResult result = CheckRunner.checkFile(filePath, uri, settings);
        checkDiags.put(uri, result.diagnostics());
        publishMerged(uri);
        // runOnFile does not use the context path so no companion diagnostics.
        // Do NOT call refreshCodeLenses() here.
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

        if (hasForeignErrors && client != null) {
            String fileName = uri.substring(uri.lastIndexOf('/') + 1);
            String msg = "OpenJML: ESC on " + fileName
                    + " could not run — type errors in: " + String.join(", ", foreignFiles);
            client.logMessage(new MessageParams(MessageType.Warning, msg));
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

    private void publishMerged(String uri) {
        List<Diagnostic> merged = new ArrayList<>();
        merged.addAll(checkDiags.getOrDefault(uri, List.of()));
        merged.addAll(escDiags.getOrDefault(uri, List.of()));
        client.publishDiagnostics(new PublishDiagnosticsParams(uri, merged));
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
}
