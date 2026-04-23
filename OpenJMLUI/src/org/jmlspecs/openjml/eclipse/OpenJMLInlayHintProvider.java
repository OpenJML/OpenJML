/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.codemining.AbstractCodeMiningProvider;
import org.eclipse.jface.text.codemining.ICodeMining;
import org.eclipse.jface.text.codemining.LineContentCodeMining;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4j.InlayHint;
import org.eclipse.lsp4j.InlayHintParams;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.eclipse.lsp4j.services.LanguageServer;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;

/**
 * Code mining provider for OpenJML inlay hints (variable type inference) in the
 * JDT Java editor.
 *
 * <p>This provider is registered via
 * {@code org.eclipse.ui.workbench.texteditor.codeMiningProviders} for
 * {@code JavaEditor} instances and calls the OpenJML LSP server directly
 * through {@link OpenJMLLanguageClient#server()}.
 *
 * <p>Note: {@link LineContentCodeMining} (inline rendering) does not visually
 * appear in the JDT Java editor even when the mining is returned.  The provider
 * is kept in place for future use; inferred types for {@code var} declarations
 * are accessible via hover (see {@link OpenJMLJavaHover}).
 */
public class OpenJMLInlayHintProvider extends AbstractCodeMiningProvider {

    /** Whole-document range used in every request. */
    private static final org.eclipse.lsp4j.Position START =
            new org.eclipse.lsp4j.Position(0, 0);
    private static final org.eclipse.lsp4j.Position END =
            new org.eclipse.lsp4j.Position(99999, 0);
    private static final Range ALL = new Range(START, END);

    @Override
    public CompletableFuture<List<? extends ICodeMining>> provideCodeMinings(
            ITextViewer viewer, IProgressMonitor monitor) {

        OpenJMLLanguageClient lc = OpenJMLCodeMiningProvider.languageClient;
        if (lc == null) return CompletableFuture.completedFuture(List.of());

        LanguageServer ls = lc.server();
        if (ls == null) return CompletableFuture.completedFuture(List.of());

        String uri = getFileUri();
        if (uri == null) return CompletableFuture.completedFuture(List.of());

        IDocument doc = viewer.getDocument();
        InlayHintParams params = new InlayHintParams(
                new TextDocumentIdentifier(uri), ALL);

        return ls.getTextDocumentService().inlayHint(params)
                .thenApply(hints -> toMinings(hints, doc));
    }

    private String getFileUri() {
        IEditorPart editor = getAdapter(IEditorPart.class);
        if (editor == null) return null;
        if (editor.getEditorInput() instanceof IFileEditorInput fei) {
            var uri = LSPEclipseUtils.toUri(fei.getFile());
            return uri != null ? uri.toString() : null;
        }
        return null;
    }

    private List<ICodeMining> toMinings(List<? extends InlayHint> hints, IDocument doc) {
        if (hints == null) return List.of();
        List<ICodeMining> result = new ArrayList<>();
        for (InlayHint hint : hints) {
            if (hint == null || hint.getLabel() == null) continue;
            String label = hint.getLabel().isLeft()
                    ? hint.getLabel().getLeft()
                    : hint.getLabel().getRight().stream()
                            .map(p -> p.getValue() != null ? p.getValue() : "")
                            .reduce("", String::concat);
            if (label.isEmpty()) continue;
            try {
                int line   = hint.getPosition().getLine();
                int col    = hint.getPosition().getCharacter();
                int offset = doc.getLineOffset(line) + col;
                Position pos = new Position(offset, 0);
                final String text = label;
                LineContentCodeMining mining = new LineContentCodeMining(pos, this) {
                    { setLabel(text); }

                    @Override
                    protected CompletableFuture<Void> doResolve(
                            ITextViewer v, IProgressMonitor m) {
                        return CompletableFuture.completedFuture(null);
                    }
                };
                result.add(mining);
            } catch (BadLocationException ignored) {}
        }
        return result;
    }
}
