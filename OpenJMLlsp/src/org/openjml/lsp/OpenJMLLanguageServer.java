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

        registry.onUri       (OpenJMLCommands.FOCUS_FILE,          textDocumentService::recheckUri);
        registry.onUriReturn (OpenJMLCommands.GET_SEMANTIC_TOKENS, textDocumentService::getSemanticTokens);
        registry.onNoArgs    (OpenJMLCommands.CLEAR_AND_REINDEX,   textDocumentService::resetAndReindex);
        registry.onNoArgs    (OpenJMLCommands.CLEAR_MARKERS,       textDocumentService::clearMarkers);
        registry.on(OpenJMLCommands.INDEX_PROJECT,        args -> { textDocumentService.indexProject(cmdProject(args)); return null; });
        registry.on(OpenJMLCommands.SYMBOLS_FOR_PROJECT,  args -> textDocumentService.symbolsForProject(str(args, 0) != null ? str(args, 0) : "", str(args, 1)));
        registry.on(OpenJMLCommands.CANCEL_ESC,           args -> { textDocumentService.cancelEsc(str(args, 0)); return null; });
        registry.on(OpenJMLCommands.ABORT_METHOD_PROOF,   args -> { textDocumentService.abortMethodProof(str(args, 0)); return null; });
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
            OpenJMLSettings.ProjectConfig wp = new OpenJMLSettings.ProjectConfig();
            wp.id        = OpenJMLSettings.WORKSPACE_PROJECT_ID;
            wp.rootPaths = folderPaths.isEmpty() ? null : folderPaths;
            globalSettings.projects = new java.util.ArrayList<>(List.of(wp));
        }
        // Populate the per-project settings registry so settingsForUri() works
        // uniformly for all clients.  Always called: after this point projectSettings
        // is never empty (at minimum it contains the "__workspace__" entry).
        textDocumentService.updateProjectSettings(globalSettings.projects);

        // Propagate capability flags — must be read after applyRaw() has populated settings.
        textDocumentService.setClientSupportsActionMessages(globalSettings.supportsActionMessages);
        var cc = params.getCapabilities();
        var ws = cc != null ? cc.getWorkspace() : null;
        var stCap = ws != null ? ws.getSemanticTokens() : null;
        textDocumentService.setClientRefreshCapabilities(
                stCap != null && Boolean.TRUE.equals(stCap.getRefreshSupport()));

        var caps = new ServerCapabilities();
        caps.setTextDocumentSync(globalSettings.incrementalSync
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

        // Advertise all registered workspace/executeCommand names so that clients
        // can validate their command-name constants against this list at startup.
        caps.setExecuteCommandProvider(new ExecuteCommandOptions(registry.commandNames()));

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

    /** Dispatches {@code openjml.runEsc}: URIs go to scheduleEscForUri, paths to scheduleEscForPaths. */
    private Object handleRunEsc(java.util.List<?> args) {
        String proj = cmdProject(args);
        List<String> uris = new java.util.ArrayList<>();
        List<String> paths = new java.util.ArrayList<>();
        for (String p : cmdPaths(args)) {
            if (p.startsWith("file://")) uris.add(p);
            else paths.add(p);
        }
        uris.forEach(uri -> textDocumentService.scheduleEscForUri(uri, proj));
        if (!paths.isEmpty()) textDocumentService.scheduleEscForPaths(paths, proj);
        return null;
    }

    /**
     * Dispatches {@code openjml.runEscForMethod}.
     * Code-lens format: {@code [uri, methodFqn]} (first arg starts with {@code file://}).
     * Standard format:  {@code [projectId, uri, methodFqn]}.
     */
    private Object handleRunEscForMethod(java.util.List<?> args) {
        final String proj, uri, method;
        if (isCodeLensFormat(args)) {
            proj = null; uri = str(args, 0); method = str(args, 1);
        } else {
            proj = str(args, 0); uri = str(args, 1); method = str(args, 2);
        }
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

    /**
     * Returns {@code true} if {@code args} uses the two-element code-lens format
     * {@code [uri, methodFqn]} emitted by {@code codeLens()} for the
     * {@code openjml.runEscForMethod} command.
     *
     * <p>Detected by: exactly two arguments whose first element starts with
     * {@code "file://"}, which is unambiguous because a project ID never
     * contains a URL scheme.
     */
    private static boolean isCodeLensFormat(java.util.List<?> args) {
        if (args == null || args.size() != 2) return false;
        String first = str(args, 0);
        return first != null && first.startsWith("file://");
    }

    /** Returns the path/URI arguments from a command (args[1+]). */
    private static List<String> cmdPaths(java.util.List<?> args) {
        return extractPaths(args, 1);
    }
}
