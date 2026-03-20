/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.action.IAction;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;

/**
 * Handles the {@code org.openjml.eclipse.findDeclaration} command (F3 in the
 * Generic Editor for {@code .jml} files).
 *
 * <p>Delegates to Eclipse's built-in "Open Hyperlink" text-editor action, which
 * invokes all registered hyperlink detectors — including LSP4E's
 * {@code OpenDeclarationHyperlinkDetector} — and navigates to the declaration
 * found via {@code textDocument/definition}.
 *
 * <p>For {@code .java} files, JDT's own F3 binding takes priority, so this
 * handler is effectively only active for {@code .jml} files in the Generic Editor.
 */
public class JmlOpenDeclarationHandler extends AbstractHandler {

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        IEditorPart editor = HandlerUtil.getActiveEditor(event);
        if (!(editor instanceof ITextEditor textEditor)) return null;
        IAction action = textEditor.getAction(ITextEditorActionConstants.OPEN_HYPERLINK);
        if (action != null && action.isEnabled()) {
            action.run();
        }
        return null;
    }
}
