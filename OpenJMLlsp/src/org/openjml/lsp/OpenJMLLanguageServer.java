package org.openjml.lsp;

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

    private final OpenJMLSettings             settings;
    private final OpenJMLTextDocumentService  textDocumentService;
    private final OpenJMLWorkspaceService     workspaceService;

    private LanguageClient client   = null;
    private int            exitCode    = 1;
    private String         rootUri     = null;
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
        this.settings            = new OpenJMLSettings();
        this.textDocumentService = new OpenJMLTextDocumentService(settings,
                OpenJMLCommands.RUN_ESC_FOR_METHOD);

        CommandRegistry registry = new CommandRegistry();

        // All commands share a fixed 4-element prefix:
        //   args[0] sourcePath, args[1] classPath, args[2] specsPath, args[3] propertiesFile
        // Command-specific arguments follow at position 4+.

        registry.on(OpenJMLCommands.CHECK_JML, args -> {
            // [sourcePath, classPath, specsPath, propertiesFile, path1, path2, ...]
            List<String> paths = extractPaths(args, 4);
            if (!paths.isEmpty()) textDocumentService.scheduleCheckForPaths(
                    paths, str(args, 0), str(args, 1), str(args, 2), str(args, 3));
            return null;
        });
        registry.on(OpenJMLCommands.RUN_ESC, args -> {
            // [sourcePath, classPath, specsPath, propertiesFile, path1, path2, ...]
            // A "path" that starts with "file://" is treated as a document URI and
            // routed to scheduleEscForUri (so it works on in-memory content);
            // all other paths are collected for a single scheduleEscForPaths call.
            List<String> uris = new java.util.ArrayList<>();
            List<String> paths = new java.util.ArrayList<>();
            for (String p : extractPaths(args, 4)) {
                if (p.startsWith("file://")) uris.add(p);
                else paths.add(p);
            }
            String src = str(args, 0), cp = str(args, 1),
                   sp  = str(args, 2), pf = str(args, 3);
            for (String uri : uris)
                textDocumentService.scheduleEscForUri(uri, src, cp, sp, pf);
            if (!paths.isEmpty())
                textDocumentService.scheduleEscForPaths(paths, src, cp, sp, pf);
            return null;
        });
        registry.on(OpenJMLCommands.RUN_ESC_FOR_METHOD, args -> {
            // [sourcePath, classPath, specsPath, propertiesFile, uri, methodFqn]
            String uri    = str(args, 4);
            String method = str(args, 5);
            if (uri != null) textDocumentService.scheduleEscForMethod(
                    uri, method, str(args, 0), str(args, 1), str(args, 2), str(args, 3));
            return null;
        });
        registry.on(OpenJMLCommands.RUN_RAC, args -> {
            // [sourcePath, classPath, specsPath, propertiesFile, outputDir, path1, path2, ...]
            List<String> paths = extractPaths(args, 5);
            if (!paths.isEmpty()) textDocumentService.scheduleRacForPaths(
                    paths, str(args, 0), str(args, 1), str(args, 2), str(args, 3), str(args, 4));
            return null;
        });

        registry.onUri       (OpenJMLCommands.FOCUS_FILE,          textDocumentService::recheckUri);
        registry.onUriReturn (OpenJMLCommands.GET_SEMANTIC_TOKENS, textDocumentService::getSemanticTokens);
        registry.onNoArgs    (OpenJMLCommands.CLEAR_AND_REINDEX,   textDocumentService::resetAndReindex);
        registry.onNoArgs    (OpenJMLCommands.CLEAR_MARKERS,       textDocumentService::clearMarkers);
        registry.on          (OpenJMLCommands.CANCEL_ESC, args -> {
            textDocumentService.cancelEsc(args.isEmpty() ? null : (String) args.get(0));
            return null;
        });
        registry.on          (OpenJMLCommands.GET_RUNNING_ESC_TASKS,
                              args -> textDocumentService.getRunningEscUris());

        this.workspaceService = new OpenJMLWorkspaceService(settings, registry,
                textDocumentService::symbols,
                textDocumentService::handleWatchedJmlChange,
                textDocumentService::handleWatchedJavaChange,
                this::reregisterFileWatchers);
    }

    @Override
    public CompletableFuture<InitializeResult> initialize(InitializeParams params) {
        workspaceService.applyRaw(params.getInitializationOptions());
        rootUri = params.getRootUri();

        // Collect workspace folder paths so CheckRunner can append them to -sourcepath.
        if (params.getWorkspaceFolders() != null) {
            String joined = params.getWorkspaceFolders().stream()
                    .map(f -> f.getUri())
                    .filter(u -> u != null && u.startsWith("file:"))
                    .map(u -> { try { return java.nio.file.Path.of(java.net.URI.create(u)).toString(); }
                                catch (Exception e) { return null; } })
                    .filter(p -> p != null)
                    .collect(java.util.stream.Collectors.joining(java.io.File.pathSeparator));
            if (!joined.isEmpty()) settings.workspaceFolderPaths = joined;
        }
        // Fall back to rootUri if no workspace folders list was provided.
        if ((settings.workspaceFolderPaths == null || settings.workspaceFolderPaths.isEmpty())
                && rootUri != null && rootUri.startsWith("file:")) {
            try {
                settings.workspaceFolderPaths =
                        java.nio.file.Path.of(java.net.URI.create(rootUri)).toString();
            } catch (Exception ignored) {}
        }

        // Auto-discover openjml.properties at the workspace root unless the
        // client already supplied an explicit propertiesFile setting.
        if ((settings.propertiesFile == null || settings.propertiesFile.isEmpty())
                && rootUri != null) {
            try {
                java.nio.file.Path candidate = java.nio.file.Path.of(
                        java.net.URI.create(rootUri)).resolve("openjml.properties");
                if (java.nio.file.Files.isRegularFile(candidate)) {
                    settings.propertiesFile = candidate.toString();
                    System.err.println("[OpenJML] Auto-discovered properties file: " + candidate);
                }
            } catch (Exception ignored) {}
        }

        var caps = new ServerCapabilities();
        caps.setTextDocumentSync(settings.incrementalSync
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
        System.err.println("[initialize] semanticTokensProvider.full=" + stOpts.getFull());

        var inlayHintsOpts = new InlayHintRegistrationOptions();
        inlayHintsOpts.setResolveProvider(false);
        caps.setInlayHintProvider(Either.forRight(inlayHintsOpts));

        return CompletableFuture.completedFuture(new InitializeResult(caps));
    }

    @Override
    public void initialized(InitializedParams params) {
        serverInitialized = true;
        // Kick off a background pass over all .java files in the workspace so
        // that workspace/symbol can find symbols in files not yet opened.
        if (rootUri != null) textDocumentService.scheduleWorkspaceIndex(rootUri);
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
     * Called when {@code jmlWorkspaceRoots} changes via {@code didChangeConfiguration}.
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
}
