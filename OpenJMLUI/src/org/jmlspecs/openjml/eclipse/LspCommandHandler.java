/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.handlers.HandlerUtil;

import com.google.gson.JsonPrimitive;

/**
 * Eclipse command handler that forwards an LSP {@code workspace/executeCommand}
 * request to the running OpenJML language server.
 *
 * <p>Subclasses (static inner classes) supply the LSP command name.
 * They are registered in {@code plugin.xml} via
 * {@code org.eclipse.ui.handlers} extension points.
 *
 * <p>Keybindings (defined in plugin.xml):
 * <ul>
 *   <li>{@code Ctrl/Cmd + Shift + J, E} — Run ESC on current file</li>
 *   <li>{@code Ctrl/Cmd + Shift + J, M} — Run ESC for method under cursor</li>
 * </ul>
 */
public abstract class LspCommandHandler extends AbstractHandler {

    protected final String lspCommand;

    protected LspCommandHandler(String lspCommand) {
        this.lspCommand = lspCommand;
    }
    
    // FIXME - need to adjust these commands to act on whatever is selected -- a file editor, or possibly multiple items in the Outline or Project Explorer or Package Explorer

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        IEditorPart editor = HandlerUtil.getActiveEditor(event);
        if (editor == null) return null;
        if (!(editor.getEditorInput() instanceof IFileEditorInput)) return null;

        IFile file = ((IFileEditorInput) editor.getEditorInput()).getFile();
        String uri  = file.getLocationURI().toString();
        
        Console.log(lspCommand);
        
        buildParams(uri, file, event).thenAccept(params -> {
            if (params == null) return;
            LanguageServers.forProject(file.getProject())
                .computeFirst(server ->
                    server.getWorkspaceService().executeCommand(params));
        });
        return null;
    }

    /**
     * Build the {@link ExecuteCommandParams} to send.  Returns a
     * {@code CompletableFuture} so subclasses can do async work (e.g. AST
     * lookups) before the params are ready.  Return {@code null} to cancel.
     */
    protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
            buildParams(String uri, IFile file, ExecutionEvent event) {
        return java.util.concurrent.CompletableFuture.completedFuture(
                new ExecuteCommandParams(lspCommand, List.of(new JsonPrimitive(uri))));
    }

    // -----------------------------------------------------------------------
    // Concrete handlers registered via plugin.xml
    // -----------------------------------------------------------------------

    /** Runs {@code openjml.checkJML} on the currently selected entities. */
    public static final class CheckJML extends LspCommandHandler {
        public CheckJML() { super("openjml.checkJML"); }
    }

    /** Runs {@code openjml.runRac} on the currently selected entities. */
    public static final class RunRac extends LspCommandHandler {
        public RunRac() { super("openjml.runRac"); }
    }

    /** Runs {@code openjml.runEsc} on the currently seelected entities. */
    public static final class RunEsc extends LspCommandHandler {
        public RunEsc() { super("openjml.runEsc"); }
    }

    /**
     * Runs {@code openjml.runEscForMethod} on the currently active editor file.
     *
     * <p>The method FQN is currently passed as an empty string; a future
     * revision can resolve the FQN from the cursor position via the AST.
     */
    public static final class RunEscForMethod extends LspCommandHandler {
        public RunEscForMethod() { super("openjml.runEscForMethod"); }

        @Override
        protected java.util.concurrent.CompletableFuture<ExecuteCommandParams>
                buildParams(String uri, IFile file, ExecutionEvent event) {
            // TODO: resolve method FQN from cursor position using JDT IMethod
            // For now send uri + empty string; the server will ESC the whole file
            // when no method name is supplied.
            return java.util.concurrent.CompletableFuture.completedFuture(
                    new ExecuteCommandParams("openjml.runEscForMethod",
                            List.of(new JsonPrimitive(uri), new JsonPrimitive(""))));
        }
    }

    /** Sends {@code openjml.clearAndReindex} (no file argument). */
    public static final class ClearAndReindex extends LspCommandHandler {
        public ClearAndReindex() { super("openjml.clearAndReindex"); }

        @Override
        public Object execute(ExecutionEvent event) {
            // FIXME - is there some way to get the unique LSP connection for the whole plugin?
            // clearAndReindex is workspace-wide; no file argument needed.
            // Use any open project to route to the server.
            IEditorPart editor = HandlerUtil.getActiveEditor(event);
            IFile file = null;
            if (editor != null && editor.getEditorInput() instanceof IFileEditorInput) {
                file = ((IFileEditorInput) editor.getEditorInput()).getFile();
            }

            Console.errorlog(lspCommand);

            if (file != null) {
                LanguageServers.forProject(file.getProject())
                    .computeFirst(server ->
                        server.getWorkspaceService().executeCommand(
                                new ExecuteCommandParams("openjml.clearAndReindex",
                                        List.of())));
            } else {
                Console.log("OpenJML: no active editor — cannot route clearAndReindex");
            }
            return null;
        }
    }
}
