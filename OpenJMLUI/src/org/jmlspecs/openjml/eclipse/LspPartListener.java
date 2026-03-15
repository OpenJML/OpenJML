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
 * LSP server by calling LSP4E's
 * {@code ConnectDocumentToLanguageServerSetupParticipant.setup(IDocument)}
 * directly.  That is the same code path LSP4E uses internally when a file is
 * opened in the Generic Editor, so it triggers server startup and
 * {@code textDocument/didOpen} exactly as if the file had been opened there.
 *
 * <p>If the primary path fails the file is opened in the Generic Editor as a
 * fallback so LSP4E's normal buffer-creation path can take over.
 *
 * <p>Registered programmatically from {@link openjmlui.Activator}.
 */
public class LspPartListener implements org.eclipse.ui.IPartListener2 {

    /** Generic Editor ID — used as fallback trigger. */
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

        // Get the document from the file buffer (already exists since JDT opened the file).
        org.eclipse.core.filebuffers.ITextFileBuffer buf =
                org.eclipse.core.filebuffers.FileBuffers.getTextFileBufferManager()
                        .getTextFileBuffer(file.getFullPath(),
                                org.eclipse.core.filebuffers.LocationKind.IFILE);
        if (buf == null) {
            System.err.println("[OpenJML] LspPartListener: no file buffer for " + file.getName()
                    + " — falling back to Generic Editor");
            openGenericEditor(file);
            return;
        }
        org.eclipse.jface.text.IDocument doc = buf.getDocument();

        // Primary: call LSP4E's own document-setup participant directly.
        // ConnectDocumentToLanguageServerSetupParticipant.setup(IDocument) is what LSP4E
        // calls internally when a file opens in the Generic Editor.  Calling it here
        // triggers the same server-startup and textDocument/didOpen flow for JDT-opened files.
        ClassLoader lsp4eLoader = openjmlui.Activator.lsp4eLoader;
        if (lsp4eLoader != null) {
            try {
                Class<?> participantClass = lsp4eLoader.loadClass(
                        "org.eclipse.lsp4e.ConnectDocumentToLanguageServerSetupParticipant");
                Object participant = participantClass.getDeclaredConstructor().newInstance();
                java.lang.reflect.Method setup = participantClass.getMethod(
                        "setup", org.eclipse.jface.text.IDocument.class);
                setup.invoke(participant, doc);
                System.err.println("[OpenJML] LspPartListener: setup() called for "
                        + file.getName());
                return;
            } catch (Throwable t) {
                System.err.println("[OpenJML] LspPartListener: setup() failed for "
                        + file.getName() + ": " + t);
                t.printStackTrace(System.err);
            }
        } else {
            System.err.println("[OpenJML] LspPartListener: lsp4e loader not ready, "
                    + "falling back to Generic Editor for " + file.getName());
        }

        // Fallback: open in Generic Editor.
        openGenericEditor(file);
    }

    private void openGenericEditor(IFile file) {
        try {
            org.eclipse.ui.IWorkbenchPage page =
                    org.eclipse.ui.PlatformUI.getWorkbench().getActiveWorkbenchWindow()
                            .getActivePage();
            if (page == null) { System.err.println("[OpenJML] LspPartListener: no active page"); return; }
            IEditorPart ge = page.openEditor(new FileEditorInput(file), GENERIC_EDITOR_ID,
                    false /* do not activate */);
            System.err.println("[OpenJML] LspPartListener: Generic Editor fallback: " + (ge != null));
        } catch (Throwable e) {
            System.err.println("[OpenJML] LspPartListener: Generic Editor fallback failed: " + e);
        }
    }
}
