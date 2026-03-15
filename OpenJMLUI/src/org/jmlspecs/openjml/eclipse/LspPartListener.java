/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.resources.IFile;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.part.FileEditorInput;

/**
 * Listens for editor opens and connects each Java/JML file to the OpenJML
 * LSP server.  The server itself is started in {@link openjmlui.Activator#earlyStartup()}
 * via {@code LanguageServiceAccessor.startLanguageServer(def)}.  This listener
 * then calls {@code getInitializedLanguageServer(file, def, null)} for each
 * newly-opened file so that LSP4E sends {@code textDocument/didOpen} and
 * begins delivering diagnostics.
 *
 * <p>Registered programmatically from {@link openjmlui.Activator}.
 */
public class LspPartListener implements org.eclipse.ui.IPartListener2 {

    /** Generic Editor ID — used as a secondary trigger if the primary approach fails. */
    private static final String GENERIC_EDITOR_ID = "org.eclipse.ui.genericeditor.GenericEditor";

    /** Files for which we have already triggered LSP startup — avoid repeat work. */
    private final java.util.Set<org.eclipse.core.runtime.IPath> triggered =
            java.util.Collections.synchronizedSet(new java.util.HashSet<>());

    @Override
    public void partOpened(IWorkbenchPartReference ref) { handlePart(ref); }

    @Override public void partActivated(IWorkbenchPartReference ref) { handlePart(ref); }
    @Override public void partBroughtToTop(IWorkbenchPartReference ref) {}
    @Override public void partClosed(IWorkbenchPartReference ref) {}
    @Override public void partDeactivated(IWorkbenchPartReference ref) {}
    @Override public void partHidden(IWorkbenchPartReference ref) {}
    @Override public void partVisible(IWorkbenchPartReference ref) {}
    @Override public void partInputChanged(IWorkbenchPartReference ref) {}

    private void handlePart(IWorkbenchPartReference ref) {
        IWorkbenchPart part = ref.getPart(false);
        if (!(part instanceof IEditorPart)) return;
        IEditorInput input = ((IEditorPart) part).getEditorInput();
        if (!(input instanceof IFileEditorInput)) return;
        IFile file = ((IFileEditorInput) input).getFile();
        String ext = file.getFileExtension();
        if (!"java".equals(ext) && !"jml".equals(ext)) return;

        org.eclipse.core.runtime.IPath path = file.getFullPath();
        if (!triggered.add(path)) return;  // already triggered for this file

        System.err.println("[OpenJML] LspPartListener: handling " + file.getName());

        // Primary approach: use LanguageServiceAccessor.getInitializedLanguageServer(file, def, null)
        // which connects the file to the already-running server and triggers textDocument/didOpen.
        Object def = openjmlui.Activator.ourLsDefinition;
        ClassLoader lsp4eLoader = openjmlui.Activator.lsp4eLoader;
        if (def != null && lsp4eLoader != null) {
            try {
                Class<?> lsaClass = lsp4eLoader.loadClass(
                        "org.eclipse.lsp4e.LanguageServiceAccessor");
                // getInitializedLanguageServer(IResource, LanguageServerDefinition, Predicate)
                java.lang.reflect.Method m = null;
                for (java.lang.reflect.Method candidate : lsaClass.getDeclaredMethods()) {
                    if ("getInitializedLanguageServer".equals(candidate.getName())
                            && candidate.getParameterCount() == 3) {
                        m = candidate;
                        break;
                    }
                }
                if (m != null) {
                    m.setAccessible(true);
                    java.util.concurrent.CompletableFuture<?> future =
                            (java.util.concurrent.CompletableFuture<?>) m.invoke(
                                    null, file, def, (java.util.function.Predicate<Object>) caps -> true);
                    future.whenComplete((server, ex) -> {
                        if (ex != null) {
                            System.err.println("[OpenJML] LspPartListener: getInitializedLanguageServer"
                                    + " error for " + file.getName() + ": " + ex);
                        } else {
                            System.err.println("[OpenJML] LspPartListener: server connected for "
                                    + file.getName() + ": "
                                    + (server != null ? server.getClass().getSimpleName() : "null"));
                        }
                    });
                    System.err.println("[OpenJML] LspPartListener: getInitializedLanguageServer"
                            + " called for " + file.getName());
                    return;
                } else {
                    System.err.println("[OpenJML] LspPartListener: getInitializedLanguageServer"
                            + " method not found");
                }
            } catch (Throwable e) {
                System.err.println("[OpenJML] LspPartListener: primary approach failed: " + e);
                e.printStackTrace(System.err);
            }
        } else {
            System.err.println("[OpenJML] LspPartListener: definition not ready yet for "
                    + file.getName() + " (def=" + def + ")");
        }

        // Fallback: open the file in the Generic Editor.  LSP4E monitors the Generic Editor
        // and may start / connect the server when it sees the file's content type there.
        try {
            org.eclipse.ui.IWorkbenchPage page =
                    org.eclipse.ui.PlatformUI.getWorkbench().getActiveWorkbenchWindow()
                            .getActivePage();
            if (page == null) {
                System.err.println("[OpenJML] LspPartListener: no active page");
                return;
            }
            IEditorPart ge = page.openEditor(new FileEditorInput(file), GENERIC_EDITOR_ID,
                    false /* do not activate */);
            System.err.println("[OpenJML] LspPartListener: fallback Generic Editor opened: "
                    + (ge != null));
        } catch (Throwable e) {
            System.err.println("[OpenJML] LspPartListener: fallback exception: " + e);
        }
    }
}
