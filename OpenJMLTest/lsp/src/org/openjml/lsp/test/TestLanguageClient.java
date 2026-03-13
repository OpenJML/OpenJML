package org.openjml.lsp.test;

import org.eclipse.lsp4j.ApplyWorkspaceEditParams;
import org.eclipse.lsp4j.ApplyWorkspaceEditResponse;
import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.MessageActionItem;
import org.eclipse.lsp4j.MessageParams;
import org.eclipse.lsp4j.PublishDiagnosticsParams;
import org.eclipse.lsp4j.RegistrationParams;
import org.eclipse.lsp4j.ShowMessageRequestParams;
import org.eclipse.lsp4j.UnregistrationParams;
import org.eclipse.lsp4j.services.LanguageClient;

import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

/**
 * Minimal in-process LSP client for use in protocol-layer tests.
 *
 * Collects {@code textDocument/publishDiagnostics} notifications in a
 * per-URI map of {@link CompletableFuture}s so that tests can block until
 * the async server check completes and then assert on the results.
 *
 * Usage:
 * <pre>
 *   testClient.awaitDiagnostics("file:///Foo.java", 30, TimeUnit.SECONDS)
 * </pre>
 *
 * Only the first {@code publishDiagnostics} notification for each URI is
 * captured.  Call {@link #reset(String)} between successive notifications
 * for the same URI if needed.
 */
public class TestLanguageClient implements LanguageClient {

    private final ConcurrentHashMap<String, CompletableFuture<List<Diagnostic>>> pending =
            new ConcurrentHashMap<>();

    /**
     * Block until the server publishes diagnostics for {@code uri}.
     *
     * @param uri     the document URI to wait for
     * @param timeout how long to wait
     * @param unit    time unit
     * @return the list of diagnostics received (may be empty for a clean file)
     */
    public List<Diagnostic> awaitDiagnostics(String uri, long timeout, TimeUnit unit)
            throws InterruptedException, ExecutionException, TimeoutException {
        return pending.computeIfAbsent(uri, k -> new CompletableFuture<>())
                      .get(timeout, unit);
    }

    /**
     * Reset the future for {@code uri} so that a subsequent
     * {@link #awaitDiagnostics} call waits for the next notification.
     */
    public void reset(String uri) {
        pending.remove(uri);
    }

    // --- LanguageClient callbacks ---

    @Override
    public void publishDiagnostics(PublishDiagnosticsParams params) {
        pending.computeIfAbsent(params.getUri(), k -> new CompletableFuture<>())
               .complete(params.getDiagnostics());
    }

    @Override
    public void telemetryEvent(Object object) {}

    @Override
    public void logMessage(MessageParams message) {}

    @Override
    public void showMessage(MessageParams messageParams) {}

    @Override
    public CompletableFuture<MessageActionItem> showMessageRequest(
            ShowMessageRequestParams requestParams) {
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> registerCapability(RegistrationParams params) {
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> unregisterCapability(UnregistrationParams params) {
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<ApplyWorkspaceEditResponse> applyEdit(
            ApplyWorkspaceEditParams params) {
        return CompletableFuture.completedFuture(new ApplyWorkspaceEditResponse(false));
    }
}
