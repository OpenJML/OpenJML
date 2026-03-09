package org.openjml.lsp;

import org.eclipse.lsp4j.CodeLensOptions;
import org.eclipse.lsp4j.RenameOptions;
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
 *   <li>semanticTokens — JML keyword/clause highlighting</li>
 *   <li>completion — JML keywords</li>
 * </ul>
 */
public class OpenJMLLanguageServer implements LanguageServer, LanguageClientAware {

    private final OpenJMLSettings             settings;
    private final OpenJMLTextDocumentService  textDocumentService;
    private final OpenJMLWorkspaceService     workspaceService;

    private int exitCode = 1;

    /**
     * @param escCommand           command name for full-file ESC (passed to WorkspaceService)
     * @param escForMethodCommand  command name for per-method ESC (passed to WorkspaceService and TextDocumentService)
     */
    public OpenJMLLanguageServer(String escCommand, String escForMethodCommand) {
        this.settings            = new OpenJMLSettings();
        this.textDocumentService = new OpenJMLTextDocumentService(settings, escForMethodCommand);
        this.workspaceService    = new OpenJMLWorkspaceService(settings,
                textDocumentService::scheduleEscForUri,
                textDocumentService::scheduleEscForMethod,
                escCommand,
                escForMethodCommand);
    }

    @Override
    public CompletableFuture<InitializeResult> initialize(InitializeParams params) {
        workspaceService.applyRaw(params.getInitializationOptions());

        var caps = new ServerCapabilities();
        caps.setTextDocumentSync(TextDocumentSyncKind.Full);
        caps.setCodeLensProvider(new CodeLensOptions(false));
        caps.setHoverProvider(Boolean.TRUE);
        caps.setDefinitionProvider(Boolean.TRUE);
        caps.setDeclarationProvider(Boolean.TRUE);
        caps.setReferencesProvider(Boolean.TRUE);
        caps.setRenameProvider(new RenameOptions(true));  // prepareProvider=true

        return CompletableFuture.completedFuture(new InitializeResult(caps));
    }

    @Override
    public void initialized(InitializedParams params) {}

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
