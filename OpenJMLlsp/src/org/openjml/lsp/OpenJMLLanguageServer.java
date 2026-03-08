package org.openjml.lsp;

import org.eclipse.lsp4j.CodeLensOptions;
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

    private final OpenJMLSettings             settings            = new OpenJMLSettings();
    private final OpenJMLTextDocumentService  textDocumentService = new OpenJMLTextDocumentService(settings);
    private final OpenJMLWorkspaceService     workspaceService    =
            new OpenJMLWorkspaceService(settings,
                    textDocumentService::scheduleEscForUri,
                    textDocumentService::scheduleEscForMethod);

    private int exitCode = 1;

    @Override
    public CompletableFuture<InitializeResult> initialize(InitializeParams params) {
        workspaceService.applyRaw(params.getInitializationOptions());

        var caps = new ServerCapabilities();
        caps.setTextDocumentSync(TextDocumentSyncKind.Full);
        // Do NOT advertise openjml.runEsc in executeCommandProvider.
        // If we did, vscode-languageclient's ExecuteCommandFeature would auto-register
        // the VS Code command and invoke it with no arguments, so the URI would never
        // be passed to the server.  Instead the extension registers the command manually
        // and sends workspace/executeCommand with the active file's URI explicitly.
        caps.setCodeLensProvider(new CodeLensOptions(false));
        caps.setHoverProvider(Boolean.TRUE);

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
