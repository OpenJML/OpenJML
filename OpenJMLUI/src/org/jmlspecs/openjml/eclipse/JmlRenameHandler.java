/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.net.URI;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.RenameParams;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * Handles the {@code org.openjml.eclipse.commands.rename} command and also
 * overrides JDT's {@code org.eclipse.jdt.ui.edit.text.java.rename.element}
 * in OpenJML-natured projects (see plugin.xml handler registration).
 *
 * <p>Prompts the user for a new name via an {@link InputDialog}, then calls
 * {@code textDocument/rename} on the OpenJML LSP server via LSP4E and applies
 * the returned {@link org.eclipse.lsp4j.WorkspaceEdit} — updating all Java
 * and JML reference sites atomically via
 * {@link LSPEclipseUtils#applyWorkspaceEdit}.
 *
 * <p>Works for both {@code .java} files (open in the JDT Java editor) and
 * {@code .jml} files (open in the Generic Editor), as long as the OpenJML
 * LSP server is connected to the document.
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
                .thenAccept(optEdit -> optEdit.ifPresent(edit ->
                        Display.getDefault().asyncExec(() ->
                                LSPEclipseUtils.applyWorkspaceEdit(edit, label))))
                .exceptionally(t -> {
                    Throwable cause = t.getCause() != null ? t.getCause() : t;
                    Display.getDefault().asyncExec(() ->
                            MessageDialog.openError(shell, "Rename Failed", cause.getMessage()));
                    return null;
                });

        return null;
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
