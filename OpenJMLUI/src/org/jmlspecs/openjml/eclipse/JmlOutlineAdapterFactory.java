/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.core.runtime.Platform;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.ServerCapabilities;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

/**
 * Adapter factory that provides an {@link IContentOutlinePage} for {@code .jml}
 * files opened in Eclipse's Generic Editor.
 *
 * <p>LSP4E's built-in {@code EditorToOutlineAdapterFactory} waits only 50 ms for the
 * language server to confirm {@code documentSymbolProvider} capability.  On a cold
 * start (first file open) the OpenJML LSP server takes longer to initialize, causing
 * the factory to return {@code null} and Eclipse to display "There is no active editor
 * that provides an outline."
 *
 * <p>This factory intercepts requests for {@code .jml} files, waits up to 5 s for the
 * server to respond, then delegates back to the adapter manager (with a re-entrancy
 * guard so it skips itself) so that LSP4E's factory can take its fast-path with the
 * server already active.
 */
public class JmlOutlineAdapterFactory implements IAdapterFactory {

    /** Re-entrancy guard: prevents infinite loops when we call the adapter manager below. */
    private static final ThreadLocal<Boolean> inProgress = ThreadLocal.withInitial(() -> Boolean.FALSE);

    @Override
    @SuppressWarnings("unchecked")
    public <T> T getAdapter(Object adaptable, Class<T> adapterType) {
        if (inProgress.get()) return null;
        if (adapterType != IContentOutlinePage.class) return null;
        if (!(adaptable instanceof IEditorPart editor)) return null;

        IEditorInput input = editor.getEditorInput();
        if (!(input instanceof IFileEditorInput fei)) return null;
        IFile file = fei.getFile();
        if (!"jml".equals(file.getFileExtension())) return null;

        var doc = LSPEclipseUtils.getDocument(input);
        if (doc == null) return null;

        // Wait up to 5 seconds for the LSP server to become ready.
        // We use computeFirst with a documentSymbol capability filter so that
        // LSP4E also caches this wrapper for the editor.
        try {
            LanguageServers.forDocument(doc)
                .withCapability(ServerCapabilities::getDocumentSymbolProvider)
                .computeFirst(ls -> CompletableFuture.completedFuture(ls))
                .get(5, TimeUnit.SECONDS);
        } catch (Exception e) {
            // Timed out or error — proceed and let LSP4E's factory handle it.
        }

        // Re-invoke the adapter manager; our guard causes this instance to return
        // null, so LSP4E's EditorToOutlineAdapterFactory runs next.  By now the
        // server is active, so that factory takes its fast path and returns the
        // CNFOutlinePage immediately.
        inProgress.set(Boolean.TRUE);
        try {
            return (T) Platform.getAdapterManager().getAdapter(adaptable, IContentOutlinePage.class);
        } finally {
            inProgress.remove();
        }
    }

    @Override
    public Class<?>[] getAdapterList() {
        return new Class<?>[] { IContentOutlinePage.class };
    }
}
