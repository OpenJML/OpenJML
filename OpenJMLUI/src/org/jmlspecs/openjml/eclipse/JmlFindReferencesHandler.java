/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.handlers.IHandlerService;

/**
 * Handles the {@code org.openjml.eclipse.commands.findReferences} command
 * (Shift+Ctrl+G in the Generic Editor for {@code .jml} files).
 *
 * <p>Delegates to the Generic Editor's built-in
 * {@code org.eclipse.ui.genericeditor.findReferences} command, which is
 * handled by LSP4E's {@code LSFindReferences} handler whenever the active
 * editor has a language server.  LSP4E calls {@code textDocument/references}
 * on the OpenJML LSP server and displays the results in Eclipse's Search
 * view.
 *
 * <p>For {@code .java} files, JDT's own Shift+Ctrl+G binding takes priority;
 * this handler is effectively only active for {@code .jml} files in the
 * Generic Editor.
 */
public class JmlFindReferencesHandler extends AbstractHandler {

    private static final String FIND_REFS_CMD =
            "org.eclipse.ui.genericeditor.findReferences";

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        IHandlerService hs = HandlerUtil.getActivePart(event)
                .getSite().getService(IHandlerService.class);
        try {
            hs.executeCommand(FIND_REFS_CMD, null);
        } catch (Exception e) {
            // command not available (no language server active) — ignore
        }
        return null;
    }
}
