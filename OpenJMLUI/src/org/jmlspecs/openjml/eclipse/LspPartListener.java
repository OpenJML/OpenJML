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
 * Listens for editor opens and triggers the OpenJML LSP server for Java and JML
 * files by briefly opening the file in the Generic Editor, which LSP4E monitors.
 *
 * <p>LSP4E only auto-starts language servers when files are opened in the Generic
 * Editor.  JDT's CompilationUnitEditor is invisible to LSP4E's startup mechanism.
 * This listener compensates by opening each Java/JML file once in the Generic
 * Editor (in the background, without stealing focus) so that LSP4E detects the
 * content type and starts the OpenJML server.  The Generic Editor tab is closed
 * immediately; the server process continues running.
 *
 * <p>Registered programmatically from {@link openjmlui.Activator}.
 */
public class LspPartListener implements org.eclipse.ui.IPartListener2 {

    /** Generic Editor ID — LSP4E monitors documents opened here. */
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

        // Log content types so we can verify LSP4E's content-type matching.
        try {
            org.eclipse.core.runtime.content.IContentType[] cts =
                    org.eclipse.core.runtime.Platform.getContentTypeManager()
                            .findContentTypesFor(file.getName());
            StringBuilder ctIds = new StringBuilder();
            for (org.eclipse.core.runtime.content.IContentType ct : cts) {
                if (ctIds.length() > 0) ctIds.append(", ");
                ctIds.append(ct.getId());
            }
            System.err.println("[OpenJML] LspPartListener: content types for "
                    + file.getName() + ": [" + ctIds + "]");
        } catch (Throwable t) {
            System.err.println("[OpenJML] LspPartListener: content type lookup failed: " + t);
        }

        System.err.println("[OpenJML] LspPartListener: triggering LSP for " + file.getName());

        // Open the file in the Generic Editor (background, no focus steal).
        // LSP4E monitors Generic Editor document events and will start the OpenJML
        // server based on the file's content type.  We close the tab immediately;
        // the server process keeps running.
        try {
            org.eclipse.ui.IWorkbenchPage page =
                    org.eclipse.ui.PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
            if (page == null) {
                System.err.println("[OpenJML] LspPartListener: no active page");
                return;
            }
            // Open in background (activate=false keeps focus on the JDT editor).
            // The Generic Editor tab stays open alongside JDT's editor — LSP4E uses
            // it to track the document and send textDocument/didOpen to the server.
            // The user can close the tab manually; the server will restart on the
            // next file open if needed.
            IEditorPart ge = page.openEditor(new FileEditorInput(file), GENERIC_EDITOR_ID,
                    false /* do not activate */);
            System.err.println("[OpenJML] LspPartListener: Generic Editor opened: " + (ge != null));

            // Explicitly start the LSP server via LanguageServers.computeFirst().
            // LSP4E's Generic Editor does NOT auto-start servers merely by being opened;
            // a call through LanguageServers API is needed to instantiate the provider.
            org.eclipse.core.filebuffers.ITextFileBuffer buf =
                    org.eclipse.core.filebuffers.FileBuffers.getTextFileBufferManager()
                            .getTextFileBuffer(file.getFullPath(),
                                    org.eclipse.core.filebuffers.LocationKind.IFILE);
            if (buf != null) {
                org.eclipse.jface.text.IDocument doc = buf.getDocument();
                System.err.println("[OpenJML] LspPartListener: requesting server via computeFirst for "
                        + file.getName());
                org.eclipse.lsp4e.LanguageServers.forDocument(doc)
                        .computeFirst(ls -> {
                            System.err.println("[OpenJML] LspPartListener: server obtained for "
                                    + file.getName() + ": " + ls.getClass().getSimpleName());
                            return java.util.concurrent.CompletableFuture.completedFuture(
                                    Boolean.TRUE);
                        })
                        .whenComplete((result, ex) -> {
                            if (ex != null) {
                                System.err.println("[OpenJML] LspPartListener: computeFirst error: "
                                        + ex);
                            } else {
                                System.err.println("[OpenJML] LspPartListener: computeFirst result: "
                                        + result);
                            }
                        });
            } else {
                System.err.println("[OpenJML] LspPartListener: no file buffer for " + file.getName());
            }
        } catch (Throwable e) {
            System.err.println("[OpenJML] LspPartListener exception: " + e);
            e.printStackTrace(System.err);
        }
    }
}
