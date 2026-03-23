package org.openjml.lsp;

import org.eclipse.lsp4j.CodeLensOptions;
import org.eclipse.lsp4j.CompletionOptions;
import org.eclipse.lsp4j.RenameOptions;
import org.eclipse.lsp4j.SemanticTokensLegend;
import org.eclipse.lsp4j.SemanticTokensWithRegistrationOptions;
import org.eclipse.lsp4j.InitializeParams;
import org.eclipse.lsp4j.InitializeResult;
import org.eclipse.lsp4j.InitializedParams;
import org.eclipse.lsp4j.ServerCapabilities;
import org.eclipse.lsp4j.TextDocumentSyncKind;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.LanguageClientAware;
import org.eclipse.lsp4j.services.LanguageServer;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.eclipse.lsp4j.services.WorkspaceService;

import java.util.List;
import java.util.concurrent.CompletableFuture;

/**
 * Top-level LSP server for OpenJML.
 *
 * Capabilities:
 * <ul>
 *   <li>textDocumentSync: Full</li>
 *   <li>codeLens: per-method ESC status (verified / issues / checking)</li>
 *   <li>hover: JML spec for the method under the cursor</li>
 * </ul>
 *
 * Configuration is received via {@code initialize} ({@code initializationOptions})
 * and {@code workspace/didChangeConfiguration}.
 *
 * Future capabilities (not yet implemented):
 * <ul>
 *   <li>completion — JML keywords</li>
 * </ul>
 */
public class OpenJMLLanguageServer implements LanguageServer, LanguageClientAware {

    private final OpenJMLSettings             settings;
    private final OpenJMLTextDocumentService  textDocumentService;
    private final OpenJMLWorkspaceService     workspaceService;

    private int    exitCode = 1;
    private String rootUri  = null;

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
        registry.onUri       (OpenJMLCommands.RUN_ESC,             textDocumentService::scheduleEscForUri);
        registry.onUriStr    (OpenJMLCommands.RUN_ESC_FOR_METHOD,  textDocumentService::scheduleEscForMethod);
        registry.onStringList(OpenJMLCommands.RUN_ESC_DIR,         textDocumentService::scheduleEscForPaths);
        registry.onUri       (OpenJMLCommands.FOCUS_FILE,          textDocumentService::recheckUri);
        registry.onUriReturn (OpenJMLCommands.GET_SEMANTIC_TOKENS, textDocumentService::getSemanticTokens);
        registry.onUriStr    (OpenJMLCommands.RUN_RAC,             (uri, dir) -> textDocumentService.scheduleRacForUri(uri, dir));
        registry.onNoArgs    (OpenJMLCommands.CLEAR_AND_REINDEX,   textDocumentService::resetAndReindex);
        registry.onNoArgs    (OpenJMLCommands.CLEAR_MARKERS,       textDocumentService::clearMarkers);

        this.workspaceService = new OpenJMLWorkspaceService(settings, registry,
                textDocumentService::symbols);
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
        caps.setTextDocumentSync(TextDocumentSyncKind.Full);
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

        // Semantic tokens for non-VS Code clients (Neovim, Eclipse LSP4E, etc.).
        // In VS Code the extension uses a directly-registered provider instead to
        // avoid being overwritten by the Red Hat Java extension's semantic tokens.
        var stLegend = new SemanticTokensLegend(
                SemanticTokensProvider.TOKEN_TYPES,
                SemanticTokensProvider.TOKEN_MODIFIERS);
        var stOpts = new SemanticTokensWithRegistrationOptions(stLegend, Boolean.TRUE);
        caps.setSemanticTokensProvider(stOpts);
        System.err.println("[initialize] semanticTokensProvider.full=" + stOpts.getFull());

        return CompletableFuture.completedFuture(new InitializeResult(caps));
    }

    @Override
    public void initialized(InitializedParams params) {
        // Kick off a background pass over all .java files in the workspace so
        // that workspace/symbol can find symbols in files not yet opened.
        if (rootUri != null) textDocumentService.scheduleWorkspaceIndex(rootUri);
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
        textDocumentService.connect(client);
    }
}
