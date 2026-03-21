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
 * Handles the {@code org.openjml.eclipse.commands.rename} command and also
 * overrides JDT's {@code org.eclipse.jdt.ui.edit.text.java.rename.element}
 * in OpenJML-natured projects (see plugin.xml handler registration).
 *
 * <p>Delegates to LSP4E's built-in
 * {@code org.eclipse.ui.edit.rename} command, which is handled by
 * {@code LSPRenameHandler} whenever the active editor has a language server.
 * LSP4E prompts for the new name, calls {@code textDocument/rename} on the
 * OpenJML LSP server, and applies the returned {@link org.eclipse.lsp4j.WorkspaceEdit}
 * — updating all Java and JML reference sites in one step.
 *
 * <p>For {@code .java} files in non-OpenJML projects, JDT's own Alt+Shift+R
 * binding takes priority; this handler is active only when the OpenJML
 * project nature is present (enforced by the {@code activeWhen} expression in
 * plugin.xml) or when invoked explicitly from the OpenJML menu.
 */
public class JmlRenameHandler extends AbstractHandler {

    private static final String RENAME_CMD = "org.eclipse.ui.edit.rename";

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        IHandlerService hs = HandlerUtil.getActivePart(event)
                .getSite().getService(IHandlerService.class);
        try {
            hs.executeCommand(RENAME_CMD, null);
        } catch (Exception e) {
            // command not available (no language server active) — ignore
        }
        return null;
    }
}
