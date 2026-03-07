package org.openjml.lsp;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DidChangeTextDocumentParams;
import org.eclipse.lsp4j.DidCloseTextDocumentParams;
import org.eclipse.lsp4j.DidOpenTextDocumentParams;
import org.eclipse.lsp4j.DidSaveTextDocumentParams;
import org.eclipse.lsp4j.PublishDiagnosticsParams;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.TextDocumentService;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;

/**
 * Handles text document lifecycle notifications.
 *
 * <p>Two independent checks are run per document: a fast {@code --check} pass
 * and a slower {@code --esc} pass.  Each has its own trigger setting and its
 * own debounce delay.  Their diagnostics are merged before publishing so that
 * neither pass's results overwrite the other's.
 *
 * <p><b>--check trigger</b> ({@link OpenJMLSettings#checkTriggerOn}):
 * <ul>
 *   <li>{@code "edit"} (default) — check on open and every change (debounced {@value #CHECK_DEBOUNCE_MS} ms)</li>
 *   <li>{@code "save"} — check on open and save only</li>
 * </ul>
 * In both modes check always runs on open and save.
 *
 * <p><b>--esc trigger</b> ({@link OpenJMLSettings#escTriggerOn}):
 * <ul>
 *   <li>{@code "manual"} (default) — only on explicit {@code openjml.runEsc} command</li>
 *   <li>{@code "save"} — on every save</li>
 *   <li>{@code "edit"} — on every change (debounced {@value #ESC_DEBOUNCE_MS} ms; expensive)</li>
 * </ul>
 * In "edit" and "save" modes ESC also runs when the file is first opened.
 *
 * <p>Text document sync mode is {@code Full}.
 */
public class OpenJMLTextDocumentService implements TextDocumentService {

    /** Debounce delay for --check in edit mode. */
    static final long CHECK_DEBOUNCE_MS = 500;

    /** Debounce delay for --esc in edit mode (longer — ESC is expensive). */
    static final long ESC_DEBOUNCE_MS = 2000;

    private final OpenJMLSettings settings;
    private LanguageClient client;

    private final ExecutorService          executor  = Executors.newCachedThreadPool();
    private final ScheduledExecutorService scheduler = Executors.newSingleThreadScheduledExecutor();

    /** Pending debounce futures for --check, keyed by URI. */
    private final Map<String, ScheduledFuture<?>> pendingCheck = new ConcurrentHashMap<>();

    /** Pending debounce futures for --esc, keyed by URI. */
    private final Map<String, ScheduledFuture<?>> pendingEsc   = new ConcurrentHashMap<>();

    /** Latest --check diagnostics per URI. */
    private final Map<String, List<Diagnostic>> checkDiags = new ConcurrentHashMap<>();

    /** Latest --esc diagnostics per URI. */
    private final Map<String, List<Diagnostic>> escDiags   = new ConcurrentHashMap<>();

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

        // --check: always on open
        scheduleCheckNow(uri, content);

        // --esc: on open if not manual
        if (!settings.isEscManual()) {
            scheduleEscNow(uri, content);
        }
    }

    @Override
    public void didChange(DidChangeTextDocumentParams params) {
        if (params.getContentChanges().isEmpty()) return;
        String uri     = params.getTextDocument().getUri();
        String content = params.getContentChanges().get(0).getText();

        // --check: debounced if in edit mode
        if (settings.isCheckOnEdit()) {
            debounce(pendingCheck, uri,
                    () -> runCheckContent(uri, content),
                    CHECK_DEBOUNCE_MS);
        }

        // --esc: debounced if in edit mode
        if (settings.isEscOnEdit()) {
            debounce(pendingEsc, uri,
                    () -> runEscContent(uri, content),
                    ESC_DEBOUNCE_MS);
        }
    }

    @Override
    public void didSave(DidSaveTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        cancelPending(uri);

        // --check: always on save
        scheduleCheckFile(uri);

        // --esc: on save if escTriggerOn == "save"
        if (settings.isEscOnSave()) {
            scheduleEscFile(uri);
        }
    }

    @Override
    public void didClose(DidCloseTextDocumentParams params) {
        String uri = params.getTextDocument().getUri();
        cancelPending(uri);
        checkDiags.remove(uri);
        escDiags.remove(uri);
        client.publishDiagnostics(new PublishDiagnosticsParams(uri, List.of()));
    }

    /**
     * Run ESC on the given URI immediately (for the {@code openjml.runEsc} command).
     * Uses the file on disk; if the file does not exist the call is a no-op.
     */
    void scheduleEscForUri(String uri) {
        scheduleEscFile(uri);
    }

    // --- scheduling helpers ---

    private void scheduleCheckNow(String uri, String content) {
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath != null && new java.io.File(filePath).exists()) {
            scheduleCheckFile(uri);
        } else {
            executor.submit(() -> runCheckContent(uri, content));
        }
    }

    private void scheduleEscNow(String uri, String content) {
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath != null && new java.io.File(filePath).exists()) {
            scheduleEscFile(uri);
        } else {
            executor.submit(() -> runEscContent(uri, content));
        }
    }

    private void scheduleCheckFile(String uri) {
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath == null) return;
        executor.submit(() -> runCheckFile(filePath, uri));
    }

    private void scheduleEscFile(String uri) {
        String filePath = CheckRunner.uriToPath(uri);
        if (filePath == null) return;
        executor.submit(() -> runEscFile(filePath, uri));
    }

    // --- runners (execute on the thread pool) ---

    private void runCheckContent(String uri, String content) {
        List<Diagnostic> diags = CheckRunner.check(uri, content, settings);
        checkDiags.put(uri, diags);
        publishMerged(uri);
    }

    private void runEscContent(String uri, String content) {
        List<Diagnostic> diags = CheckRunner.runEsc(uri, content, settings);
        escDiags.put(uri, diags);
        publishMerged(uri);
    }

    private void runCheckFile(String filePath, String uri) {
        List<Diagnostic> diags = CheckRunner.checkFile(filePath, uri, settings);
        checkDiags.put(uri, diags);
        publishMerged(uri);
    }

    private void runEscFile(String filePath, String uri) {
        List<Diagnostic> diags = CheckRunner.runEscFile(filePath, uri, settings);
        escDiags.put(uri, diags);
        publishMerged(uri);
    }

    // --- diagnostic merging ---

    private void publishMerged(String uri) {
        List<Diagnostic> merged = new ArrayList<>();
        merged.addAll(checkDiags.getOrDefault(uri, List.of()));
        merged.addAll(escDiags.getOrDefault(uri, List.of()));
        client.publishDiagnostics(new PublishDiagnosticsParams(uri, merged));
    }

    // --- debounce / cancel helpers ---

    private void debounce(Map<String, ScheduledFuture<?>> map, String uri,
                          Runnable task, long delayMs) {
        ScheduledFuture<?> prev = map.put(uri,
                scheduler.schedule(() -> {
                    map.remove(uri);
                    executor.submit(task);
                }, delayMs, TimeUnit.MILLISECONDS));
        if (prev != null) prev.cancel(false);
    }

    private void cancelPending(String uri) {
        ScheduledFuture<?> c = pendingCheck.remove(uri);
        if (c != null) c.cancel(false);
        ScheduledFuture<?> e = pendingEsc.remove(uri);
        if (e != null) e.cancel(false);
    }
}
