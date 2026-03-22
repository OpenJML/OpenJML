/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.lang.reflect.Method;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.jface.text.IDocument;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.ServerCapabilities;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;

/**
 * Adapter factory that provides an {@code IContentOutlinePage} for {@code .jml}
 * files opened in Eclipse's Generic Editor.
 *
 * <p>LSP4E's built-in {@code EditorToOutlineAdapterFactory} waits only 50 ms for the
 * language server to confirm {@code documentSymbolProvider} capability.  On a cold
 * start the OpenJML LSP server may take longer to initialize, causing the factory to
 * return {@code null} and Eclipse to display "There is no active editor that provides
 * an outline."
 *
 * <p>This factory uses a two-path strategy:
 * <ol>
 *   <li><b>Fast path</b>: if the server is already started (wrapper cached by
 *       {@link LspPartListener}), reflectively call
 *       {@code EditorToOutlineAdapterFactory.createOutlinePage} immediately.</li>
 *   <li><b>Slow path</b>: server not yet ready — return {@code null} immediately
 *       (non-blocking) and schedule an async task that waits for the server, then
 *       re-activates the editor so the Outline View re-queries the adapter.</li>
 * </ol>
 */
public class JmlOutlineAdapterFactory implements IAdapterFactory {

    @Override
    @SuppressWarnings("unchecked")
    public <T> T getAdapter(Object adaptable, Class<T> adapterType) {
        if (!"org.eclipse.ui.views.contentoutline.IContentOutlinePage"
                .equals(adapterType.getName())) return null;
        if (!(adaptable instanceof IEditorPart editor)) return null;

        IEditorInput input = editor.getEditorInput();
        if (!(input instanceof IFileEditorInput fei)) return null;
        IFile file = fei.getFile();
        if (!"jml".equals(file.getFileExtension())) return null;

        ClassLoader loader = org.openjml.ui.Activator.lsp4eLoader;
        if (loader == null) return null;

        // Fast path: server wrapper already cached by LspPartListener.
        Object wrapper = LspPartListener.cachedWrapper;
        if (wrapper != null) {
            Object page = tryCreateOutlinePage(loader, editor, wrapper);
            if (page != null) return adapterType.cast(page);
        }

        // Slow path: server not yet ready.  Return null now (must not block the SWT thread)
        // and schedule an async task that waits for the server, then triggers a re-query of
        // this adapter by re-activating the editor (which fires partActivated → ContentOutline
        // calls editor.getAdapter again, taking the fast path above).
        IDocument doc = LSPEclipseUtils.getDocument(input);
        if (doc != null) {
            CompletableFuture.runAsync(() -> {
                try {
                    LanguageServers.forDocument(doc)
                            .withCapability(ServerCapabilities::getDocumentSymbolProvider)
                            .computeFirst(ls -> CompletableFuture.completedFuture(ls))
                            .get(10, TimeUnit.SECONDS);
                } catch (Exception e) {
                    return;
                }
                // Back on UI thread — re-activate the editor so ContentOutline refreshes.
                Display.getDefault().asyncExec(() -> {
                    try {
                        var page = editor.getSite().getPage();
                        if (page.getActiveEditor() == editor) page.activate(editor);
                    } catch (Exception ignored) {}
                });
            });
        }

        return null;
    }

    /**
     * Reflectively calls {@code EditorToOutlineAdapterFactory.createOutlinePage(IEditorPart, wrapper)}.
     * Returns the {@code CNFOutlinePage} or {@code null} on failure.
     */
    private static Object tryCreateOutlinePage(ClassLoader loader, IEditorPart editor, Object wrapper) {
        try {
            Class<?> factoryClass = loader.loadClass(
                    "org.eclipse.lsp4e.outline.EditorToOutlineAdapterFactory");
            for (Method m : factoryClass.getDeclaredMethods()) {
                if ("createOutlinePage".equals(m.getName()) && m.getParameterCount() == 2) {
                    m.setAccessible(true);
                    return m.invoke(null, editor, wrapper);
                }
            }
        } catch (Exception e) {
            System.err.println("[OpenJML] JmlOutlineAdapterFactory: createOutlinePage failed: " + e);
        }
        return null;
    }

    @Override
    public Class<?>[] getAdapterList() {
        // IContentOutlinePage may not be on our bundle classpath if the OSGi wiring
        // hasn't resolved org.eclipse.ui.views.  The plugin.xml declaration is sufficient
        // for Eclipse's AdapterManager to route requests; this method is only used for
        // validation.  Return the class if we can load it, empty array otherwise.
        try {
            return new Class<?>[] { Class.forName(
                    "org.eclipse.ui.views.contentoutline.IContentOutlinePage",
                    false, Thread.currentThread().getContextClassLoader()) };
        } catch (ClassNotFoundException | NoClassDefFoundError e) {
            return new Class<?>[0];
        }
    }
}
