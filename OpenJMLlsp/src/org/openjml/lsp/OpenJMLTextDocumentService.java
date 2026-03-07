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
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;

/**
 * Handles text document lifecycle notifications with a hybrid check strategy.
 *
 * <p>Two trigger modes are supported via {@link OpenJMLSettings#triggerOn}:
 * <ul>
 *   <li><b>edit</b> (default) — a check is scheduled on every {@code didChange};
 *       the current editor buffer (possibly unsaved) is written to a temp file
 *       and passed to OpenJML.  The file on disk is used for {@code didOpen}
 *       and {@code didSave}.</li>
 *   <li><b>save</b> — checks only on {@code didOpen} and {@code didSave}, using
 *       the file on disk directly.  {@code didChange} marks the document dirty
 *       so the editor knows diagnostics may be stale, but does not run OpenJML.
 *       This avoids per-keystroke overhead for large projects.</li>
 * </ul>
 *
 * <p>In both modes {@code didOpen} and {@code didSave} always trigger a check
 * using the file on disk (no temp file needed, no content transfer).
 *
 * <p>Text document sync mode is {@code Full}: each change notification carries
 * the complete current content so that the temp-file path is always accurate.
 *
 * <p>In edit mode, {@code didChange} notifications are <em>debounced</em>:
 * the check is scheduled with a {@value #DEBOUNCE_MS}-millisecond delay and
 * any preceding pending check for the same URI is cancelled.  This avoids
 * spawning a full OpenJML invocation on every keystroke.
 */
public class OpenJMLTextDocumentService implements TextDocumentService {

    /** Delay before an edit-mode check fires after the last keystroke. */
    static final long DEBOUNCE_MS = 500;

    private final OpenJMLSettings settings;
    private LanguageClient client;
    private final ExecutorService          executor  = Executors.newCachedThreadPool();
    private final ScheduledExecutorService scheduler = Executors.newSingleThreadScheduledExecutor();

    /** Pending debounce futures, keyed by URI. */
    private final Map<String, ScheduledFuture<?>> pending = new ConcurrentHashMap<>();

    /** URIs that have unsaved edits since the last save or open. */
    private final Set<String> dirtyUris = ConcurrentHashMap.newKeySet();

    public OpenJMLTextDocumentService(OpenJMLSettings settings) {
        this.settings = settings;
    }

    public void connect(LanguageClient client) {
        this.client = client;
    }

    @Override
    public void didOpen(DidOpenTextDocumentParams params) {
        String uri     = params.getTextDocument().getUri();
        String content = params.getTextDocument().getText();
        dirtyUris.remove(uri);
        // Prefer disk when the file exists (normal case); fall back to the
        // content provided in the notification for untitled or in-memory files.
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath != null && new java.io.File(filePath).exists()) {
            scheduleCheckFile(uri);
        } else {
            scheduleCheckContent(uri, content);
        }
    }

    @Override
    public void didChange(DidChangeTextDocumentParams params) {
        if (params.getContentChanges().isEmpty()) return;
        String uri     = params.getTextDocument().getUri();
        String content = params.getContentChanges().get(0).getText();
        dirtyUris.add(uri);
        if (settings.isEditTriggered()) {
            // edit mode: debounce — cancel any prior pending check and reschedule.
            ScheduledFuture<?> prev = pending.put(uri,
                    scheduler.schedule(() -> {
                        pending.remove(uri);
                        List<Diagnostic> diags = CheckRunner.check(uri, content, settings);
                        client.publishDiagnostics(new PublishDiagnosticsParams(uri, diags));
                    }, DEBOUNCE_MS, TimeUnit.MILLISECONDS));
            if (prev != null) prev.cancel(false);
        }
        // save mode: do nothing until didSave fires.
    }

    @Override
    public void didSave(DidSaveTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        dirtyUris.remove(uri);
        cancelPending(uri);
        // File just saved: disk now matches editor — use disk directly.
        scheduleCheckFile(uri);
    }

    @Override
    public void didClose(DidCloseTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        dirtyUris.remove(uri);
        cancelPending(uri);
        client.publishDiagnostics(new PublishDiagnosticsParams(uri, List.of()));
    }

    // --- scheduling helpers ---

    /** Check the file on disk (no temp file). Used for open and save. */
    private void scheduleCheckFile(String uri) {
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath == null) {
            // Non-file URI (e.g. untitled:) — fall back to content-based check.
            return;
        }
        executor.submit(() -> {
            List<Diagnostic> diagnostics = CheckRunner.checkFile(filePath, uri, settings);
            client.publishDiagnostics(new PublishDiagnosticsParams(uri, diagnostics));
        });
    }

    /** Check in-memory content via a temp file. Used for untitled/in-memory files on open. */
    private void scheduleCheckContent(String uri, String content) {
        executor.submit(() -> {
            List<Diagnostic> diagnostics = CheckRunner.check(uri, content, settings);
            client.publishDiagnostics(new PublishDiagnosticsParams(uri, diagnostics));
        });
    }

    /** Cancel any pending debounced check for the given URI (e.g. on save or close). */
    private void cancelPending(String uri) {
        ScheduledFuture<?> f = pending.remove(uri);
        if (f != null) f.cancel(false);
    }
}
