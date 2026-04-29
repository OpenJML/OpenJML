/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Consumer;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.codemining.AbstractCodeMiningProvider;
import org.eclipse.jface.text.codemining.ICodeMining;
import org.eclipse.jface.text.codemining.LineHeaderCodeMining;
import org.eclipse.lsp4j.CodeLens;
import org.eclipse.lsp4j.CodeLensParams;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.eclipse.lsp4j.services.LanguageServer;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;

/**
 * Code mining provider for OpenJML ESC proof status in the JDT Java editor.
 *
 * <p>LSP4E's built-in {@code CodeLensProvider} is registered with
 * {@code enabledWhen: editorHasLanguageServer}, which only matches the generic
 * text editor — not the JDT Java editor.  As a result, no {@code codeLens}
 * request is ever sent for {@code .java} files even though
 * {@code updateCodeMinings()} is called.
 *
 * <p>This provider is registered for {@code JavaEditor} instances via
 * {@code plugin.xml} and bypasses LSP4E's document-routing entirely by calling
 * {@link OpenJMLLanguageClient#server()} directly.
 *
 * <p>{@link #languageClient} is set by
 * {@link OpenJMLLanguageClient#setDiagnosticsConsumer} when the server connects.
 */
public class OpenJMLCodeMiningProvider extends AbstractCodeMiningProvider {

    /** Set by {@link OpenJMLLanguageClient#setDiagnosticsConsumer} on connect. */
    static volatile OpenJMLLanguageClient languageClient;

    /**
     * Generation counter incremented on every {@code provideCodeMinings} call.
     * When the server calls {@code refreshCodeLenses} twice in rapid succession
     * (e.g. CHECKING start then VERIFIED completion), both calls arrive before
     * either future resolves.  Without this guard Eclipse accumulates results
     * from both futures, showing duplicate minings per method.
     * Only the latest generation's result is applied; earlier ones return an
     * empty list so Eclipse clears any stale minings.
     */
    private final AtomicLong generation = new AtomicLong();

    @Override
    public CompletableFuture<List<? extends ICodeMining>> provideCodeMinings(
            ITextViewer viewer, IProgressMonitor monitor) {

        OpenJMLLanguageClient lc = languageClient;
        if (lc == null) return CompletableFuture.completedFuture(List.of());

        LanguageServer ls = lc.server();
        if (ls == null) return CompletableFuture.completedFuture(List.of());

        String uri = getFileUri();
        if (uri == null) return CompletableFuture.completedFuture(List.of());

        IDocument doc = viewer.getDocument();
        CodeLensParams params = new CodeLensParams(new TextDocumentIdentifier(uri));
        final long myGen = generation.incrementAndGet();
        return ls.getTextDocumentService().codeLens(params)
                .thenApply(lenses -> {
                    // Discard stale results: a newer provideCodeMinings call has
                    // already been issued, so applying this result would duplicate.
                    if (generation.get() != myGen) return List.<ICodeMining>of();
                    return toMinings(lenses, doc);
                });
    }

    private String getFileUri() {
        IEditorPart editor = getAdapter(IEditorPart.class);
        if (editor == null) return null;
        if (editor.getEditorInput() instanceof IFileEditorInput fei) {
            // Use LSPEclipseUtils.toUri() — not IFile.getLocationURI().toString().
            // IFile.getLocationURI() produces "file:/path" (single slash) while LSP4E's
            // didOpen uses "file:///path" (triple slash); the server keys lastContent and
            // methodEscStatus by the triple-slash form, so we must match it.
            var uri = LSPEclipseUtils.toUri(fei.getFile());
            return uri != null ? uri.toString() : null;
        }
        return null;
    }

    private List<ICodeMining> toMinings(List<? extends CodeLens> lenses, IDocument doc) {
        if (lenses == null) return List.of();
        List<ICodeMining> result = new ArrayList<>();
        for (CodeLens lens : lenses) {
            if (lens.getCommand() == null || lens.getCommand().getTitle() == null) continue;
            int line = lens.getRange().getStart().getLine();
            final String title = lens.getCommand().getTitle();
            final String commandId = lens.getCommand().getCommand();
            final List<Object> commandArgs = lens.getCommand().getArguments() != null
                    ? new ArrayList<>(lens.getCommand().getArguments()) : List.of();
            try {
                // Wire a click action when the lens has an executable command.
                Consumer<MouseEvent> action = (commandId != null && !commandId.isEmpty()) ? e -> {
                    OpenJMLLanguageClient lc = languageClient;
                    LanguageServer ls = lc != null ? lc.server() : null;
                    if (ls == null) return;
                    ls.getWorkspaceService().executeCommand(
                            new ExecuteCommandParams(commandId, commandArgs));
                } : null;
                LineHeaderCodeMining mining = new LineHeaderCodeMining(line, doc, this, action) {
                    { setLabel(title); }
                };
                result.add(mining);
            } catch (BadLocationException ignored) {}
        }
        return result;
    }
}
