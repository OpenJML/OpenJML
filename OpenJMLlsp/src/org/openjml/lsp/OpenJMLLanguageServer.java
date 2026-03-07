package org.openjml.lsp;

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
 * Initial capabilities:
 *   - textDocumentSync: Full (complete document text on each change)
 *
 * Configuration is received via {@code initialize} ({@code initializationOptions})
 * and {@code workspace/didChangeConfiguration}, and is forwarded to
 * {@link CheckRunner} on every check invocation.
 *
 * Future capabilities (not yet implemented):
 *   - semanticTokens (JML keyword/clause highlighting)
 *   - hover (JML spec for method under cursor)
 *   - completion (JML keywords)
 *   - codeAction ("Run ESC on this method")
 */
public class OpenJMLLanguageServer implements LanguageServer, LanguageClientAware {

    private final OpenJMLSettings settings                       = new OpenJMLSettings();
    private final OpenJMLTextDocumentService textDocumentService = new OpenJMLTextDocumentService(settings);
    private final OpenJMLWorkspaceService workspaceService       = new OpenJMLWorkspaceService(settings);
    private LanguageClient client;
    private int exitCode = 1;

    @Override
    public CompletableFuture<InitializeResult> initialize(InitializeParams params) {
        // Apply any settings supplied in initializationOptions.
        workspaceService.applyRaw(params.getInitializationOptions());
        var caps = new ServerCapabilities();
        caps.setTextDocumentSync(TextDocumentSyncKind.Full);
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
        this.client = client;
        textDocumentService.connect(client);
    }
}
