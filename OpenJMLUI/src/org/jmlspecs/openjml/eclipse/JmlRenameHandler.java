/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.net.URI;
import java.util.List;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.RenameParams;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.eclipse.lsp4j.TextEdit;
import org.eclipse.lsp4j.WorkspaceEdit;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.ITextFileBuffer;
import org.eclipse.core.filebuffers.LocationKind;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * Handles the {@code org.openjml.eclipse.commands.rename} command and also
 * overrides JDT's {@code org.eclipse.jdt.ui.edit.text.java.rename.element}
 * in OpenJML-natured projects (see plugin.xml handler registration).
 *
 * <p>Prompts the user for a new name via an {@link InputDialog}, sends a
 * {@code textDocument/rename} request to the OpenJML LSP server via LSP4E,
 * and applies the returned {@link org.eclipse.lsp4j.WorkspaceEdit}.
 *
 * <h3>Why we do not delegate to {@code LSPEclipseUtils.applyWorkspaceEdit}</h3>
 *
 * <p>LSP4E only sends {@code textDocument/didOpen} to the server for the
 * <em>currently active</em> editor.  Files that are open in other editor tabs
 * (e.g. a {@code .jml} companion file visible in the editor area but not
 * focused) are <em>not</em> registered in LSP4E's internal document registry.
 *
 * <p>{@link org.eclipse.lsp4e.LSPEclipseUtils#applyWorkspaceEdit} checks that
 * registry to decide how to apply each entry in a {@code WorkspaceEdit}:
 * <ul>
 *   <li>Tracked documents (received {@code didOpen}) — edits are applied to
 *       the live {@code IDocument} buffer, leaving the editor dirty.</li>
 *   <li>Untracked documents — LSP4E falls back to {@code TextFileChange},
 *       which writes directly to disk; the editor reloads silently as saved.
 *       LSP4E may also open a new editor window for the written file.</li>
 * </ul>
 * Both of these untracked-document behaviours are wrong for our use case:
 * non-active open editors (e.g. {@code A.jml}) should become dirty, and
 * closed files should be written to disk <em>without</em> opening a new
 * editor window.
 *
 * <h3>What we do instead — mimicking JDT refactoring behaviour</h3>
 *
 * <p>For each file in the {@code WorkspaceEdit} we check the Eclipse workbench
 * directly (via {@code IWorkbenchPage.findEditors}) for any open editor:
 * <ul>
 *   <li><b>Open editor found</b> — we retrieve the document from the editor's
 *       own {@code IDocumentProvider} (the exact {@code IDocument} instance the
 *       editor tracks for dirty state) and apply the edits directly to it.
 *       Using {@code LSPEclipseUtils.getDocument(IFile)} is not sufficient here
 *       because it may return a different {@code IDocument} instance that is not
 *       connected to the editor's dirty-state mechanism.</li>
 *   <li><b>No open editor</b> — three strategies are possible; currently using (1):
 *   <ol>
 *     <li><b>Write to disk</b> ({@link #applyEditsToDisk}): simple, no new tabs.
 *         If JDT incremental build is enabled the builder will compile the
 *         just-written file against the still-on-disk (pre-rename) versions of its
 *         dependencies and produce a spurious Java error marker until the user saves
 *         all files.  Harmless when incremental build is disabled.</li>
 *     <li><b>Open background editor tab</b> ({@link #openEditorAndApplyEdits}):
 *         opens the file with {@code activate=false} so focus is not stolen, and
 *         applies edits to the buffer.  No disk write, so no JDT build is triggered.
 *         Unwanted for large renames that touch many files (many new tabs).</li>
 *     <li><b>Save all atomically</b>: save all modified editor buffers to disk
 *         and write all non-editor files inside a single {@code IWorkspace.run()}
 *         to give JDT one consistent snapshot.  Removes dirty-editor state (undo
 *         via local history only), matching JDT's own rename-refactoring behaviour.
 *         </li>
 *   </ol>
 *   Which strategy is best depends on whether incremental build is enabled and how
 *   many files the rename touches.  A future preference could expose the choice.
 *   </li>
 * </ul>
 */
public class JmlRenameHandler extends AbstractHandler {

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {

        IEditorPart editor = HandlerUtil.getActiveEditor(event);
        if (editor == null) return null;

        var resource = org.eclipse.ui.ide.ResourceUtil.getResource(editor.getEditorInput());
        if (resource == null) return null;

        IDocument doc = LSPEclipseUtils.getDocument(resource);
        if (doc == null) return null;

        ITextSelection sel = (ITextSelection)
                editor.getSite().getSelectionProvider().getSelection();
        int offset = sel.getOffset();

        URI docUri = LSPEclipseUtils.toUri(doc);
        if (docUri == null) return null;

        Position pos;
        try {
            pos = LSPEclipseUtils.toPosition(offset, doc);
        } catch (BadLocationException e) {
            return null;
        }

        // Pre-fill the dialog with the Java identifier at the cursor.
        String currentName = getWordAtOffset(doc, offset);

        // execute() is called on the UI thread — show the dialog synchronously.
        Shell shell = HandlerUtil.getActiveShell(event);
        InputDialog dialog = new InputDialog(
                shell,
                "Rename",
                "New name for '" + currentName + "':",
                currentName,
                name -> name == null || name.trim().isEmpty() ? "Name cannot be empty" : null);

        if (dialog.open() != Window.OK) return null;
        String newName = dialog.getValue().trim();
        if (newName.isEmpty() || newName.equals(currentName)) return null;

        TextDocumentIdentifier tdi = new TextDocumentIdentifier(docUri.toString());
        RenameParams params = new RenameParams(tdi, pos, newName);
        String label = "Rename '" + currentName + "' to '" + newName + "'";

        LanguageServers.forDocument(doc)
                .computeFirst(server -> server.getTextDocumentService().rename(params))
                .thenAccept(optEdit -> optEdit.ifPresent(edit -> {
                        int totalEdits = edit.getChanges() != null
                                ? edit.getChanges().values().stream().mapToInt(List::size).sum() : 0;
                        Console.log("Rename to '" + newName + "': " + totalEdits + " edit(s)");
                        Display.getDefault().asyncExec(() ->
                                applyWorkspaceEditPreservingDirty(edit, label));
                }))
                .exceptionally(t -> {
                    Throwable cause = t.getCause() != null ? t.getCause() : t;
                    Display.getDefault().asyncExec(() ->
                            MessageDialog.openError(shell, "Rename Failed", cause.getMessage()));
                    return null;
                });

        return null;
    }

    /**
     * Apply a {@link WorkspaceEdit}, mimicking JDT refactoring behaviour.
     *
     * <p>See the class-level Javadoc for the full explanation of why we cannot
     * delegate to {@code LSPEclipseUtils.applyWorkspaceEdit} and what we do
     * instead.  Must be called on the UI thread.
     */
    private void applyWorkspaceEditPreservingDirty(WorkspaceEdit edit, String label) {
        if (edit.getChanges() == null) return;

        for (Map.Entry<String, List<TextEdit>> e : edit.getChanges().entrySet()) {
            String fileUri = e.getKey();
            List<TextEdit> textEdits = e.getValue();

            IDocument openDoc = findOpenEditorDocument(fileUri);
            if (openDoc != null) {
                // File is open in an editor — apply to buffer (marks dirty, no disk write).
                applyEditsToDocument(openDoc, textEdits, fileUri);
            } else {
                // File has no open editor — write to disk without opening a new editor tab.
                // Note: if JDT incremental build is enabled for this project, this will
                // trigger a build of the just-written file against the still-on-disk (pre-rename)
                // versions of its dependencies, producing a spurious Java error marker until
                // the user saves all rename-affected files.  Disable incremental build on the
                // project, or use openEditorAndApplyEdits / applyEditsAndSave variants, to
                // avoid this.  See JmlRenameHandler class javadoc for a discussion of the
                // three possible strategies.
                applyEditsToDisk(fileUri, textEdits);
            }
        }
    }

    /**
     * Open {@code fileUri} in a non-activating editor tab and apply {@code textEdits}
     * to its buffer, leaving the file dirty.
     *
     * <p>This avoids writing to disk before all rename-affected files are saved
     * together.  If a disk write happened first, JDT would immediately trigger an
     * incremental build of the just-written file against the still-on-disk (pre-rename)
     * versions of its dependencies, producing spurious Java error markers that only
     * disappear when the user saves all files.
     *
     * <p>{@code activate=false} opens the tab without stealing focus from the active
     * editor.  If the editor cannot be opened, falls back to a direct disk write via
     * {@link #applyEditsToDisk}.
     */
    private static void openEditorAndApplyEdits(String fileUri, List<TextEdit> textEdits) {
        try {
            IPath filePath = new Path(URI.create(fileUri).getPath());
            IFile ifile = org.eclipse.core.resources.ResourcesPlugin.getWorkspace()
                    .getRoot().getFileForLocation(filePath);
            if (ifile == null) {
                Console.errorlog("Rename: IFile not found: " + fileUri);
                return;
            }
            IWorkbenchPage page = null;
            for (org.eclipse.ui.IWorkbenchWindow w : PlatformUI.getWorkbench().getWorkbenchWindows()) {
                page = w.getActivePage();
                if (page != null) break;
            }
            if (page == null) {
                applyEditsToDisk(fileUri, textEdits);
                return;
            }
            // Open without activating so focus stays on the current editor.
            IEditorPart ep = IDE.openEditor(page, ifile, false);
            if (ep instanceof ITextEditor te) {
                IDocument doc = te.getDocumentProvider().getDocument(ep.getEditorInput());
                if (doc != null) {
                    applyEditsToDocument(doc, textEdits, fileUri);
                    return;
                }
            }
            applyEditsToDisk(fileUri, textEdits);
        } catch (Exception ex) {
            Console.errorlog("Rename: error opening editor for " + fileUri, ex);
        }
    }

    /**
     * Fallback: apply {@code textEdits} to the file at {@code fileUri} by reading
     * its current on-disk content, patching it in memory, and writing back via
     * {@link IFile#setContents} — without opening an editor window.
     *
     * <p>{@code keepHistory=true} preserves the pre-rename version in Eclipse's
     * local file history, making the change undoable even without an open editor.
     *
     * <p>This is used only when {@link #openEditorAndApplyEdits} cannot open an
     * editor (e.g. no active workbench page).
     */
    private static void applyEditsToDisk(String fileUri, List<TextEdit> textEdits) {
        try {
            IPath filePath = new Path(URI.create(fileUri).getPath());
            IFile ifile = org.eclipse.core.resources.ResourcesPlugin.getWorkspace()
                    .getRoot().getFileForLocation(filePath);
            if (ifile == null) {
                Console.errorlog("Rename: IFile not found for disk write: " + fileUri);
                return;
            }
            String charset = ifile.getCharset();
            String content;
            try (java.io.InputStream in = ifile.getContents()) {
                content = new String(in.readAllBytes(), charset);
            }
            // Apply edits to a temporary in-memory document.
            IDocument tmp = new Document(content);
            applyEditsToDocument(tmp, textEdits, fileUri);
            // Write back — keep file history so the change is undoable; do not force.
            byte[] bytes = tmp.get().getBytes(charset);
            ifile.setContents(new java.io.ByteArrayInputStream(bytes),
                    false /* force */, true /* keepHistory */, null);
        } catch (Exception ex) {
            Console.errorlog("Rename: error writing to disk for " + fileUri, ex);
        }
    }

    /**
     * Return the live {@link IDocument} buffer for {@code fileUri} if the file
     * is currently open in any workbench editor, or {@code null} if it is not.
     *
     * <p>The document is retrieved from the editor's own
     * {@code IDocumentProvider} rather than via
     * {@code LSPEclipseUtils.getDocument(IFile)}.  The latter may return a
     * different {@code IDocument} instance (from a separate file-buffer
     * connection) that is not the object the editor watches for dirty-state
     * changes — meaning a {@code replace()} call on it would not mark the
     * editor dirty.
     */
    private static IDocument findOpenEditorDocument(String fileUri) {
        IPath filePath;
        try {
            filePath = new Path(URI.create(fileUri).getPath());
        } catch (Exception e) {
            Console.errorlog("Rename: bad URI: " + fileUri, e);
            return null;
        }
        IFile ifile = org.eclipse.core.resources.ResourcesPlugin.getWorkspace()
                .getRoot().getFileForLocation(filePath);
        if (ifile == null) return null;

        FileEditorInput input = new FileEditorInput(ifile);
        for (org.eclipse.ui.IWorkbenchWindow window : PlatformUI.getWorkbench().getWorkbenchWindows()) {
            for (IWorkbenchPage page : window.getPages()) {
                IEditorReference[] refs = page.findEditors(input, null, IWorkbenchPage.MATCH_INPUT);
                for (IEditorReference ref : refs) {
                    // getEditor(false) returns null for lazy-restored tabs (the editor
                    // part has not been created yet, so no document provider or file
                    // buffer is connected).  getEditor(true) forces materialization
                    // without stealing focus — the active editor is unchanged.
                    IEditorPart ep = ref.getEditor(false);
                    if (ep == null) ep = ref.getEditor(true);
                    if (ep instanceof ITextEditor) {
                        // Get the document from the editor's own provider — this is the same
                        // IDocument instance the editor uses for dirty-state tracking.
                        IDocument editorDoc = ((ITextEditor) ep).getDocumentProvider()
                                .getDocument(ep.getEditorInput());
                        if (editorDoc != null) return editorDoc;
                    }
                    // ep is still null or not an ITextEditor — try the file-buffer
                    // manager as a last resort.
                    ITextFileBuffer buf = FileBuffers.getTextFileBufferManager()
                            .getTextFileBuffer(ifile.getFullPath(), LocationKind.IFILE);
                    if (buf != null) return buf.getDocument();
                }
            }
        }
        return null;
    }

    /**
     * Apply {@code textEdits} to {@code doc} in descending position order
     * so that earlier offsets remain valid after each replacement.
     */
    private static void applyEditsToDocument(IDocument doc, List<TextEdit> textEdits, String fileUri) {
        try {
            java.util.List<TextEdit> sorted = new java.util.ArrayList<>(textEdits);
            sorted.sort(java.util.Comparator
                    .<TextEdit, Integer>comparing(te -> te.getRange().getStart().getLine())
                    .thenComparingInt(te -> te.getRange().getStart().getCharacter())
                    .reversed());
            for (TextEdit te : sorted) {
                int start = toDocOffset(doc, te.getRange().getStart());
                int end   = toDocOffset(doc, te.getRange().getEnd());
                doc.replace(start, end - start, te.getNewText());
            }
        } catch (Exception ex) {
            Console.errorlog("Rename: error applying edits to buffer for " + fileUri, ex);
        }
    }

    /** Convert an LSP {@link Position} (0-based line + character) to an {@link IDocument} offset. */
    private static int toDocOffset(IDocument doc, Position pos)
            throws BadLocationException {
        return doc.getLineOffset(pos.getLine()) + pos.getCharacter();
    }

    /**
     * Extract the Java identifier word surrounding {@code offset} in {@code doc}.
     * Returns an empty string if the offset is not within an identifier.
     */
    private static String getWordAtOffset(IDocument doc, int offset) {
        try {
            int start = offset;
            while (start > 0 && Character.isJavaIdentifierPart(doc.getChar(start - 1)))
                start--;
            int end = offset;
            while (end < doc.getLength() && Character.isJavaIdentifierPart(doc.getChar(end)))
                end++;
            return doc.get(start, end - start);
        } catch (BadLocationException e) {
            return "";
        }
    }
}
