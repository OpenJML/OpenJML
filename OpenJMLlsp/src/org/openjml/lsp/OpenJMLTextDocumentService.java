package org.openjml.lsp;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DidChangeTextDocumentParams;
import org.eclipse.lsp4j.DidCloseTextDocumentParams;
import org.eclipse.lsp4j.DidOpenTextDocumentParams;
import org.eclipse.lsp4j.DidSaveTextDocumentParams;
import org.eclipse.lsp4j.PublishDiagnosticsParams;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.TextDocumentService;

import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * Handles text document lifecycle notifications.
 *
 * On {@code didOpen} and {@code didChange}, a fresh OpenJML check is
 * scheduled asynchronously; results are published back to the client
 * via {@code textDocument/publishDiagnostics}.
 *
 * Text document sync mode is {@code Full}: each change notification
 * carries the complete current content of the document.
 */
public class OpenJMLTextDocumentService implements TextDocumentService {

    private LanguageClient client;
    private final ExecutorService executor = Executors.newCachedThreadPool();

    public void connect(LanguageClient client) {
        this.client = client;
    }

    @Override
    public void didOpen(DidOpenTextDocumentParams params) {
        String uri     = params.getTextDocument().getUri();
        String content = params.getTextDocument().getText();
        scheduleCheck(uri, content);
    }

    @Override
    public void didChange(DidChangeTextDocumentParams params) {
        if (params.getContentChanges().isEmpty()) return;
        String uri     = params.getTextDocument().getUri();
        String content = params.getContentChanges().get(0).getText();
        scheduleCheck(uri, content);
    }

    @Override
    public void didClose(DidCloseTextDocumentParams params) {
        // Clear diagnostics when the editor closes the document.
        client.publishDiagnostics(
                new PublishDiagnosticsParams(params.getTextDocument().getUri(), List.of()));
    }

    @Override
    public void didSave(DidSaveTextDocumentParams params) {
        // The check is already triggered by didChange; nothing extra on save.
    }

    private void scheduleCheck(String uri, String content) {
        executor.submit(() -> {
            List<Diagnostic> diagnostics = CheckRunner.check(uri, content);
            client.publishDiagnostics(new PublishDiagnosticsParams(uri, diagnostics));
        });
    }
}
