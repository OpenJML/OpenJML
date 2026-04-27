package org.openjml.lsp;

import org.eclipse.lsp4j.ExecuteCommandOptions;
import org.eclipse.lsp4j.CodeLensOptions;
import org.eclipse.lsp4j.CompletionOptions;
import org.eclipse.lsp4j.DidChangeWatchedFilesRegistrationOptions;
import org.eclipse.lsp4j.FileSystemWatcher;
import org.eclipse.lsp4j.InlayHintRegistrationOptions;
import org.eclipse.lsp4j.Registration;
import org.eclipse.lsp4j.RegistrationParams;
import org.eclipse.lsp4j.RenameOptions;
import org.eclipse.lsp4j.SignatureHelpOptions;
import org.eclipse.lsp4j.SemanticTokensLegend;
import org.eclipse.lsp4j.SemanticTokensWithRegistrationOptions;
import org.eclipse.lsp4j.Unregistration;
import org.eclipse.lsp4j.UnregistrationParams;
import org.eclipse.lsp4j.WatchKind;
import org.eclipse.lsp4j.InitializeParams;
import org.eclipse.lsp4j.InitializeResult;
import org.eclipse.lsp4j.InitializedParams;
import org.eclipse.lsp4j.ServerCapabilities;
import org.eclipse.lsp4j.TextDocumentSyncKind;
import org.eclipse.lsp4j.WorkspaceServerCapabilities;
import org.eclipse.lsp4j.WorkspaceFoldersOptions;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.LanguageClientAware;
import org.eclipse.lsp4j.services.LanguageServer;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.eclipse.lsp4j.services.WorkspaceService;

import java.util.List;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;

/**
 * Top-level LSP server for OpenJML.
 *
 * Capabilities:
 * <ul>
 *   <li>textDocumentSync: Full</li>
 *   <li>codeLens: per-method ESC status (verified / issues / checking)</li>
 *   <li>hover: JML spec for the method under the cursor</li>
 *   <li>completion: JML keywords (triggers: {@code \}, {@code @})</li>
 *   <li>documentSymbol, foldingRange, workspaceSymbol</li>
 *   <li>definition, declaration, references, rename (with prepareRename)</li>
 *   <li>signatureHelp: parameter hints for method calls</li>
 *   <li>semanticTokens/full: JML keyword, macro, and variable highlighting</li>
 * </ul>
 *
 * Configuration is received via {@code initialize} ({@code initializationOptions})
 * and {@code workspace/didChangeConfiguration}.
 */
public class OpenJMLLanguageServer implements LanguageServer, LanguageClientAware {

    private static final String WATCHER_REGISTRATION_ID = "openjml-file-watchers";

    private final OpenJMLSettings             globalSettings;
    private final OpenJMLTextDocumentService  textDocumentService;
    private final OpenJMLWorkspaceService     workspaceService;

    private final CommandRegistry      registry;
    private LanguageClient client   = null;
    private int            exitCode    = 1;
    /** Set to {@code true} when the {@code initialized} notification arrives.
     *  Guards dynamic-capability calls that must not fire during {@code initialize}. */
    private volatile boolean serverInitialized = false;

    /**
     * Constructs the server, wiring all command names from {@link OpenJMLCommands}.
     *
     * <p>The {@code openjml.*} command names are shared constants used by both the
     * VS Code extension and the Eclipse plugin — no caller-supplied names are needed.
     */
    public OpenJMLLanguageServer() {
        this.globalSettings      = new OpenJMLSettings();
        this.textDocumentService = new OpenJMLTextDocumentService(globalSettings,
                OpenJMLCommands.RUN_ESC_FOR_METHOD);

        CommandRegistry registry = this.registry = new CommandRegistry();

        // Command argument format: args[0] = projectId (or "" for global/single-project settings),
        //                          args[1+] = command-specific paths/URIs.

        registry.on(OpenJMLCommands.CHECK_JML, args -> {
            List<String> paths = cmdPaths(args);
            if (!paths.isEmpty()) textDocumentService.scheduleCheckForPaths(paths, cmdProject(args));
            return null;
        });
        registry.on(OpenJMLCommands.RUN_ESC,            this::handleRunEsc);
        registry.on(OpenJMLCommands.RUN_ESC_FOR_METHOD, this::handleRunEscForMethod);
        registry.on(OpenJMLCommands.RUN_ESC_SPLIT_BY_FILE, args -> {
            List<String> paths = cmdPaths(args);
            if (!paths.isEmpty()) textDocumentService.scheduleEscSplitByFile(paths, cmdProject(args));
            return null;
        });
        registry.on(OpenJMLCommands.RUN_ESC_SPLIT_BY_METHOD, args -> {
            List<String> paths = cmdPaths(args);
            if (!paths.isEmpty()) textDocumentService.scheduleEscSplitByMethod(paths, cmdProject(args));
            return null;
        });
        registry.on(OpenJMLCommands.RUN_RAC, args -> {
            List<String> paths = cmdPaths(args);
            if (!paths.isEmpty()) textDocumentService.scheduleRacForPaths(paths, cmdProject(args), null);
            return null;
        });

        // FOCUS_FILE: args[0] = projectId, args[1] = uri (same convention as other commands).
        registry.on(OpenJMLCommands.FOCUS_FILE, args -> {
            String uri = str(args, 1);
            if (uri != null) textDocumentService.recheckUri(uri, str(args, 0));
            return Boolean.TRUE;
        });
        // GET_SEMANTIC_TOKENS: args[0]=projectId, args[1]=uri
        registry.on(OpenJMLCommands.GET_SEMANTIC_TOKENS, args -> {
            String uri = str(args, 1);
            return uri != null ? textDocumentService.getSemanticTokens(uri) : null;
        });
        registry.onNoArgs    (OpenJMLCommands.CLEAR_AND_REINDEX,   textDocumentService::resetAndReindex);
        registry.onNoArgs    (OpenJMLCommands.CLEAR_MARKERS,          textDocumentService::clearMarkers);
        // CLEAR_MARKERS_FOR_URIS: args[0]=projectId, args[1+]=uris
        registry.on(OpenJMLCommands.CLEAR_MARKERS_FOR_URIS, args -> {
            List<String> uris = extractPaths(args, 1);
            if (!uris.isEmpty()) textDocumentService.clearMarkersForUris(uris);
            return Boolean.TRUE;
        });
        registry.on(OpenJMLCommands.INDEX_PROJECT,        args -> { textDocumentService.indexProject(cmdProject(args)); return null; });
        // SYMBOLS_FOR_PROJECT: args[0]=projectId, args[1]=query
        registry.on(OpenJMLCommands.SYMBOLS_FOR_PROJECT,  args -> textDocumentService.symbolsForProject(str(args, 1) != null ? str(args, 1) : "", str(args, 0)));
        // CANCEL_ESC: args[0]=projectId, args[1]=target (optional)
        registry.on(OpenJMLCommands.CANCEL_ESC,           args -> { textDocumentService.cancelEsc(str(args, 0), str(args, 1)); return null; });
        // ABORT_METHOD_PROOF: args[0]=projectId, args[1]=uri, args[2]=rawName (optional)
        registry.on(OpenJMLCommands.ABORT_METHOD_PROOF,   args -> { textDocumentService.abortMethodProof(str(args, 1), str(args, 2)); return null; });
        // GET_RUNNING_ESC_TASKS: args[0]=projectId; server filters tasks to that project
        registry.on(OpenJMLCommands.GET_RUNNING_ESC_TASKS, args -> textDocumentService.getRunningEscUris());

        this.workspaceService = new OpenJMLWorkspaceService(globalSettings, registry,
                textDocumentService::symbols,
                textDocumentService::handleWatchedJmlChange,
                textDocumentService::handleWatchedJavaChange,
                this::reregisterFileWatchers,
                textDocumentService::updateProjectSettings);
    }

    @Override
    public CompletableFuture<InitializeResult> initialize(InitializeParams params) {
        workspaceService.applyRaw(params.getInitializationOptions());
        String rootUri = params.getRootUri();

        // If initializationOptions did not supply an explicit projects array,
        // synthesize a "__workspace__" project from the standard LSP workspace folders.
        // This unifies single-project clients (VS Code, bare LSP) into the same
        // projects-based model used by the Eclipse multi-project client.
        // The "__workspace__" project is always created: if no folder paths are
        // available its rootPaths is null, making it a wildcard that matches all files.
        if (globalSettings.projects == null || globalSettings.projects.isEmpty()) {
            List<String> folderPaths = new java.util.ArrayList<>();
            if (params.getWorkspaceFolders() != null) {
                for (var folder : params.getWorkspaceFolders()) {
                    String u = folder.getUri();
                    if (u != null && u.startsWith("file:")) {
                        try { folderPaths.add(java.nio.file.Path.of(java.net.URI.create(u)).toString()); }
                        catch (Exception ignored) {}
                    }
                }
            }
            // Fall back to rootUri when no workspace-folders list is provided.
            if (folderPaths.isEmpty() && rootUri != null && rootUri.startsWith("file:")) {
                try { folderPaths.add(java.nio.file.Path.of(java.net.URI.create(rootUri)).toString()); }
                catch (Exception ignored) {}
            }
            ProjectConfig wp = new ProjectConfig();
            wp.id        = OpenJMLSettings.WORKSPACE_PROJECT_ID;
            wp.rootPaths = folderPaths.isEmpty() ? null : folderPaths;
            globalSettings.projects = new java.util.ArrayList<>(List.of(wp));
        }
        // Populate the per-project settings registry so settingsForUri() works
        // uniformly for all clients.  Always called: after this point projectSettings
        // is never empty (at minimum it contains the "__workspace__" entry).
        textDocumentService.updateProjectSettings(globalSettings.projects);

        // Propagate capability flags — must be read after applyRaw() has populated settings.
        textDocumentService.setClientSupportsActionMessages(
                Boolean.TRUE.equals(globalSettings.clientSettings.supportsActionMessages));
        var cc = params.getCapabilities();
        var ws = cc != null ? cc.getWorkspace() : null;
        var stCap = ws != null ? ws.getSemanticTokens() : null;
        textDocumentService.setClientRefreshCapabilities(
                stCap != null && Boolean.TRUE.equals(stCap.getRefreshSupport()));

        var caps = new ServerCapabilities();
        caps.setTextDocumentSync(Boolean.TRUE.equals(globalSettings.clientSettings.incrementalSync)
                ? TextDocumentSyncKind.Incremental
                : TextDocumentSyncKind.Full);
        caps.setCodeLensProvider(new CodeLensOptions(false));
        // Trigger on '\' (backslash tokens) and '@' (entering a JML annotation).
        // The handler filters out non-JML contexts, so '@' in Java annotations
        // silently returns an empty list.
        caps.setCompletionProvider(new CompletionOptions(false, List.of("\\", "@")));
        caps.setHoverProvider(Boolean.TRUE);
        caps.setDocumentSymbolProvider(Boolean.TRUE);
        caps.setFoldingRangeProvider(Boolean.TRUE);
        caps.setWorkspaceSymbolProvider(Boolean.TRUE);
        caps.setDefinitionProvider(Boolean.TRUE);
        caps.setDeclarationProvider(Boolean.TRUE);
        caps.setReferencesProvider(Boolean.TRUE);
        caps.setDocumentHighlightProvider(Boolean.TRUE);
        caps.setRenameProvider(new RenameOptions(true));  // prepareProvider=true
        // Trigger on '(' (call open) and ',' (next argument).
        caps.setSignatureHelpProvider(new SignatureHelpOptions(List.of("(", ",")));

        // Semantic tokens for non-VS Code clients (Neovim, Eclipse LSP4E, etc.).
        // In VS Code the extension uses a directly-registered provider instead to
        // avoid being overwritten by the Red Hat Java extension's semantic tokens.
        var stLegend = new SemanticTokensLegend(
                SemanticTokensProvider.TOKEN_TYPES,
                SemanticTokensProvider.TOKEN_MODIFIERS);
        var stOpts = new SemanticTokensWithRegistrationOptions(stLegend, Boolean.TRUE);
        caps.setSemanticTokensProvider(stOpts);
        ServerLog.serverLog("[initialize] semanticTokensProvider.full=" + stOpts.getFull());

        var inlayHintsOpts = new InlayHintRegistrationOptions();
        inlayHintsOpts.setResolveProvider(false);
        caps.setInlayHintProvider(Either.forRight(inlayHintsOpts));

        // VS Code registers all user-facing commands itself via vscode.commands.registerCommand.
        // Advertising them here would cause vscode-languageclient's ExecuteCommandFeature to
        // try to register them again, producing "command already exists" errors.
        // For all other clients (Eclipse, generic) advertise the full list so they can
        // validate command names and route workspace/executeCommand requests.
        List<String> advertisedCmds = "vscode-java".equals(globalSettings.clientSettings.client)
                ? List.of() : registry.commandNames();
        caps.setExecuteCommandProvider(new ExecuteCommandOptions(advertisedCmds));

        // Advertise workspace folder support so VS Code's LanguageClient automatically
        // sends workspace/didChangeWorkspaceFolders when folders are added or removed.
        var wfOpts = new WorkspaceFoldersOptions();
        wfOpts.setSupported(true);
        wfOpts.setChangeNotifications(true);
        var workspaceCaps = new WorkspaceServerCapabilities();
        workspaceCaps.setWorkspaceFolders(wfOpts);
        caps.setWorkspace(workspaceCaps);

        return CompletableFuture.completedFuture(new InitializeResult(caps));
    }

    @Override
    public void initialized(InitializedParams params) {
        serverInitialized = true;
        // Kick off a full project check so that workspace/symbol can find symbols
        // in files not yet opened.  Only start the index if at least one source
        // root is known; avoids a spurious "no source directories" log message in
        // minimal test setups.  Uses the same scheduleWorkspaceReindex() path as
        // resetAndReindex() so both startup and clear-and-reindex go through
        // identical indexing logic.
        if (!globalSettings.effectiveRoots().isEmpty()) {
            textDocumentService.scheduleWorkspaceReindex();
        }
        // Register file watchers so the server is notified when .jml/.java files
        // change on disk outside the editor.
        registerFileWatchers();
    }

    /** Register (or re-register after unregistering) LSP file watchers. */
    private void registerFileWatchers() {
        if (client == null || !serverInitialized) return;
        var watchers = List.of(
            new FileSystemWatcher(Either.forLeft("**/*.jml")),
            new FileSystemWatcher(Either.forLeft("**/*.java"),
                    WatchKind.Create + WatchKind.Delete)
        );
        var reg = new Registration(WATCHER_REGISTRATION_ID,
                "workspace/didChangeWatchedFiles",
                new DidChangeWatchedFilesRegistrationOptions(watchers));
        client.registerCapability(new RegistrationParams(List.of(reg)));
    }

    /**
     * Called when watched roots change via {@code didChangeConfiguration} (new projects
     * list) or via {@code workspace/didChangeWorkspaceFolders}.
     * Unregisters the current file watchers then immediately re-registers them.
     * The brief overlap window is harmless because all events are root-filtered.
     */
    void reregisterFileWatchers() {
        if (client == null) return;
        client.unregisterCapability(new UnregistrationParams(List.of(
                new Unregistration(WATCHER_REGISTRATION_ID,
                        "workspace/didChangeWatchedFiles"))));
        registerFileWatchers();
    }

    @Override
    public CompletableFuture<Object> shutdown() {
        exitCode = 0;
        textDocumentService.shutdown();
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public void exit() {
        System.exit(exitCode);
    }

    @Override
    public TextDocumentService getTextDocumentService() {
        return textDocumentService;
    }

    @Override
    public WorkspaceService getWorkspaceService() {
        return workspaceService;
    }

    @Override
    public void connect(LanguageClient client) {
        this.client = client;
        textDocumentService.connect(client);
    }

    /** Extract the string at {@code index} from a raw LSP args list, or {@code null}. */
    private static String str(java.util.List<?> args, int index) {
        return (args != null && args.size() > index)
                ? CommandRegistry.extractString(args.get(index)) : null;
    }

    /**
     * Extract a variable-length list of non-empty strings from {@code args}
     * starting at {@code start}.
     */
    private static List<String> extractPaths(java.util.List<?> args, int start) {
        if (args == null || args.size() <= start) return List.of();
        var result = new java.util.ArrayList<String>();
        for (int i = start; i < args.size(); i++) {
            String p = CommandRegistry.extractString(args.get(i));
            if (p != null && !p.isEmpty()) result.add(p);
        }
        return result;
    }

    // -----------------------------------------------------------------------
    // Command handlers (extracted from constructor for readability)
    // -----------------------------------------------------------------------

    /** Dispatches {@code openjml.runEsc}: all arguments are OS file-system paths or directories. */
    private Object handleRunEsc(java.util.List<?> args) {
        String proj = cmdProject(args);
        List<String> paths = new java.util.ArrayList<>();
        for (String p : cmdPaths(args)) {
            if (p == null || p.isEmpty()) continue;
            if (p.startsWith("file://")) paths.add(p.substring("file://".length()));
            else paths.add(p);
        }
        if (!paths.isEmpty()) textDocumentService.scheduleEscForPaths(paths, proj);
        return null;
    }

    /**
     * Dispatches {@code openjml.runEscForMethod}.
     * Format: {@code [projectId, uri, methodFqn]} — always the three-element form;
     * the projectId is stored in the {@code ProofResult} when a code lens is created
     * and echoed back here, so the correct project settings are used for re-runs.
     */
    private Object handleRunEscForMethod(java.util.List<?> args) {
        String proj   = str(args, 0);
        String uri    = str(args, 1);
        String method = str(args, 2);
        if (uri != null) textDocumentService.scheduleEscForMethod(uri, method, proj);
        return null;
    }

    // -----------------------------------------------------------------------
    // Command argument helpers
    // -----------------------------------------------------------------------

    /**
     * Returns the project ID from a command's argument list.
     * {@code args[0]} is always the project ID; an empty string means
     * "use global/single-project settings".
     */
    private static String cmdProject(java.util.List<?> args) {
        if (args == null || args.isEmpty()) return null;
        return str(args, 0);
    }

    /** Returns the path/URI arguments from a command (args[1+]). */
    private static List<String> cmdPaths(java.util.List<?> args) {
        return extractPaths(args, 1);
    }
}
