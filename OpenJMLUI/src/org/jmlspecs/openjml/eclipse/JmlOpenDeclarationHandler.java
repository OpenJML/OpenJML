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
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.DefinitionParams;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.LocationLink;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.TextDocumentIdentifier;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
//import org.eclipse.ui.texteditor.ITextEditor;

/**
 * Handles the {@code org.openjml.eclipse.findDeclaration} command (F3 in the
 * Generic Editor for {@code .jml} files).
 *
 * <p>Finds the declaration of the identifier at the cursor by calling
 * {@code textDocument/definition} via the OpenJML LSP server, then opens
 * the result in an editor.  If multiple locations are returned the first
 * one is used.
 *
 * <p>For {@code .java} files, JDT's own F3 binding takes priority; this
 * handler is effectively only active for {@code .jml} files in the Generic
 * Editor.
 */
public class JmlOpenDeclarationHandler extends AbstractHandler {

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {

        IEditorPart editor = HandlerUtil.getActiveEditor(event);
        if (editor == null) return null;
        var resource = org.eclipse.ui.ide.ResourceUtil.getResource(editor.getEditorInput());
        if (resource == null) return null;
        IDocument doc = LSPEclipseUtils.getDocument(resource);
        
        ITextSelection sel = (ITextSelection)
                editor.getSite().getSelectionProvider().getSelection();
        int offset = sel.getOffset(); // 0-based character position

        URI docUri = LSPEclipseUtils.toUri(doc);

        Position pos;
        try {
            pos = LSPEclipseUtils.toPosition(offset, doc); // 0-based line and column offset
        } catch (BadLocationException e) {
            return null;
        }

        DefinitionParams params = new DefinitionParams(
                new TextDocumentIdentifier(docUri.toString()), pos);

        LanguageServers.forDocument(doc)
                .computeFirst(server ->
                        server.getTextDocumentService().definition(params))
                .thenAccept(opt -> opt.ifPresent(result -> {
                    String uri = null;
                    org.eclipse.lsp4j.Range range = null;
                    if (result.isLeft()) {
                        java.util.List<? extends Location> locs = result.getLeft();
                        if (!locs.isEmpty()) {
                            uri   = locs.get(0).getUri();
                            range = locs.get(0).getRange();
                        }
                    } else {
                        java.util.List<? extends LocationLink> links = result.getRight();
                        if (!links.isEmpty()) {
                            uri   = links.get(0).getTargetUri();
                            range = links.get(0).getTargetRange();
                        }
                    }
                    if (uri != null) {
                        final String fUri = uri;
                        final org.eclipse.lsp4j.Range fRange = range; // 0-based
                        Display.getDefault().asyncExec(() ->
                                LSPEclipseUtils.open(fUri, fRange));
                    }
                }));

        return null;
    }
}
