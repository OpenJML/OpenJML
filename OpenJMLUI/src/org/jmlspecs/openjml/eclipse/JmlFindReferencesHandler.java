/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.net.URI;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.ReferenceContext;
import org.eclipse.lsp4j.ReferenceParams;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.eclipse.search.ui.NewSearchUI;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * Handles the {@code org.openjml.eclipse.commands.findReferences} command and
 * also overrides JDT's {@code org.eclipse.jdt.ui.edit.text.java.search.references.in.workspace}
 * in OpenJML-natured projects (see plugin.xml handler registration).
 *
 * <p>Builds a {@link ReferenceParams} from the active editor's cursor position,
 * creates a {@link JmlReferencesSearchQuery}, and submits it to Eclipse's Search
 * view via {@link NewSearchUI#runQueryInBackground}.
 *
 * <p>Works for both {@code .java} files (open in the JDT Java editor) and
 * {@code .jml} files (open in the Generic Editor), as long as the OpenJML
 * LSP server is connected to the document.
 */
public class JmlFindReferencesHandler extends AbstractHandler {

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

        String symbolName = getWordAtOffset(doc, offset);

        TextDocumentIdentifier tdi = new TextDocumentIdentifier(docUri.toString());
        ReferenceParams params = new ReferenceParams(
                tdi, pos, new ReferenceContext(true));

        Shell shell = HandlerUtil.getActiveShell(event);
        JmlReferencesSearchQuery query =
                new JmlReferencesSearchQuery(doc, symbolName, params, shell);

        NewSearchUI.runQueryInBackground(query);
        return null;
    }

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
