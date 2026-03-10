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
     * @param escCommand           command name for full-file ESC
     * @param escForMethodCommand  command name for per-method ESC
     * @param escDirCommand        command name for multi-path ESC via {@code --dirs} (may be {@code null})
     * @param focusFileCommand     command name sent by the client when focus changes to an already-open file
     * @param getSemanticTokensCommand command name for semantic tokens
     */
    public OpenJMLLanguageServer(String escCommand, String escForMethodCommand, String escDirCommand,
                                  String focusFileCommand, String getSemanticTokensCommand) {
        this.settings            = new OpenJMLSettings();
        this.textDocumentService = new OpenJMLTextDocumentService(settings, escForMethodCommand);
        this.workspaceService    = new OpenJMLWorkspaceService(settings,
                textDocumentService::scheduleEscForUri,
                textDocumentService::scheduleEscForMethod,
                textDocumentService::scheduleEscForPaths,
                textDocumentService::recheckUri,
                textDocumentService::getSemanticTokens,
                textDocumentService::symbols,
                escCommand,
                escForMethodCommand,
                escDirCommand,
                focusFileCommand,
                getSemanticTokensCommand);
    }

    @Override
    public CompletableFuture<InitializeResult> initialize(InitializeParams params) {
        workspaceService.applyRaw(params.getInitializationOptions());
        rootUri = params.getRootUri();

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
        caps.setSemanticTokensProvider(
                new SemanticTokensWithRegistrationOptions(stLegend, Boolean.TRUE));

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
