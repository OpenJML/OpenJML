/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.window.Window;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4j.ExecuteCommandParams;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.eclipse.ui.handlers.HandlerUtil;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import com.google.gson.JsonPrimitive;
import com.google.gson.reflect.TypeToken;

/**
 * Handles the {@code org.openjml.eclipse.commands.findAllDeclarations} command.
 *
 * <p>Queries the OpenJML language server's declaration index for all symbols
 * whose name matches the given identifier, then presents the results in a
 * selection dialog.  Double-clicking (or pressing OK) navigates to the
 * selected declaration.
 *
 * <p><b>Identifier source:</b>
 * <ul>
 *   <li>If the active editor has a non-empty text selection that is a valid
 *       Java identifier (after trimming whitespace), that text is used directly
 *       and no dialog is shown.</li>
 *   <li>Otherwise, an input dialog is displayed so the user can type the
 *       identifier.</li>
 * </ul>
 *
 * <p><b>Coverage note:</b> The server's declaration index is populated as files
 * are opened and checked.  Use "Index Project" (OpenJML menu) to index all
 * source files in the project before searching, so that declarations in
 * unopened files are also found.
 */
public class JmlFindAllDeclarationsHandler extends AbstractHandler {

    private static final Gson GSON = new Gson();

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {

        Shell shell = HandlerUtil.getActiveShell(event);
        IEditorPart editor = HandlerUtil.getActiveEditor(event);

        // Step 1: get identifier from selection, or prompt the user.
        String identifier = getSelectedIdentifier(editor);
        if (identifier == null) {
            InputDialog dlg = new InputDialog(shell,
                    "Find All Declarations",
                    "Identifier name:",
                    "",
                    input -> isValidIdentifier(input.trim())
                            ? null : "Enter a valid Java identifier");
            if (dlg.open() != Window.OK) return null;
            identifier = dlg.getValue().trim();
            if (identifier.isEmpty()) return null;
        }

        // Capture for use in background Job (lambdas require effectively-final).
        final String query = identifier;
        final IProject project = getActiveProject(editor);

        // Step 2: query the server on a background thread, then show results.
        Job.create("Find All Declarations: " + query, (monitor) -> {
            List<SymbolInformation> results = queryDeclarations(query, project);
            Display.getDefault().asyncExec(() -> showResults(shell, query, results));
            return Status.OK_STATUS;
        }).schedule();

        return null;
    }

    // -----------------------------------------------------------------------
    // Server query
    // -----------------------------------------------------------------------

    private static List<SymbolInformation> queryDeclarations(String query, IProject project) {
        String projectRoot = (project != null && project.getLocation() != null)
                ? project.getLocation().toOSString() : null;

        // Query the server via the openjml.symbolsForProject command.
        // The server filters by project root server-side, so no client-side
        // path matching is needed.
        List<SymbolInformation> viaCommand = symbolsViaCommand(
                LspPartListener.cachedWrapper, query, projectRoot);
        if (viaCommand != null) return viaCommand;

        Console.log("Find All Declarations: server not available");
        return List.of();
    }

    /**
     * Send an {@code openjml.symbolsForProject} {@code workspace/executeCommand}
     * request to the language server via the cached {@code LanguageServerWrapper}.
     *
     * <p>Uses the same reflection approach as {@link LspCommandHandler#sendViaWrapper}
     * to obtain the server proxy from LSP4E's wrapper, then calls
     * {@code executeCommand} directly on it.  The result is a JSON array
     * deserialized into {@code List<SymbolInformation>}.
     *
     * @return the symbol list on success, or {@code null} if the wrapper is
     *         unavailable or the call fails
     */
    private static List<SymbolInformation> symbolsViaCommand(
            Object wrapper, String query, String projectRoot) {
        if (wrapper == null) return null;
        try {
            // Locate LanguageServerWrapper.getServer() by walking the class hierarchy.
            java.lang.reflect.Method getServer = null;
            for (Class<?> c = wrapper.getClass();
                    c != null && c != Object.class; c = c.getSuperclass()) {
                try {
                    getServer = c.getDeclaredMethod("getServer");
                    getServer.setAccessible(true);
                    break;
                } catch (NoSuchMethodException ignored) {}
            }
            if (getServer == null) {
                Console.log("Find All Declarations: getServer() not found on wrapper");
                return null;
            }

            Object serverFuture = getServer.invoke(wrapper);
            org.eclipse.lsp4j.services.LanguageServer server = null;
            if (serverFuture instanceof java.util.concurrent.CompletableFuture<?> cf) {
                Object result = cf.get(5, TimeUnit.SECONDS);
                if (result instanceof org.eclipse.lsp4j.services.LanguageServer ls) server = ls;
            } else if (serverFuture instanceof org.eclipse.lsp4j.services.LanguageServer ls) {
                server = ls;
            }
            if (server == null) {
                Console.log("Find All Declarations: could not obtain LanguageServer from wrapper");
                return null;
            }

            List<Object> args = new ArrayList<>();
            args.add(new JsonPrimitive(query));
            args.add(projectRoot != null ? new JsonPrimitive(projectRoot) : com.google.gson.JsonNull.INSTANCE);
            ExecuteCommandParams params = new ExecuteCommandParams(
                    OpenJMLConstants.CMD_SYMBOLS_FOR_PROJECT, args);

            Object raw = server.getWorkspaceService().executeCommand(params)
                    .get(15, TimeUnit.SECONDS);

            if (raw instanceof JsonElement je) {
                List<SymbolInformation> results = GSON.fromJson(je,
                        new TypeToken<List<SymbolInformation>>(){}.getType());
                Console.log("Find All Declarations: " + (results != null ? results.size() : 0)
                        + " result(s) for query=\"" + query + "\""
                        + (projectRoot != null ? " root=\"" + projectRoot + "\"" : ""));
                return results != null ? results : List.of();
            }
            Console.log("Find All Declarations: unexpected result type: "
                    + (raw != null ? raw.getClass().getName() : "null"));
            return List.of();
        } catch (Throwable t) {
            Console.log("Find All Declarations: command failed: " + t.getMessage());
            return null;
        }
    }

    // -----------------------------------------------------------------------
    // Result presentation
    // -----------------------------------------------------------------------

    private static void showResults(Shell shell, String query, List<SymbolInformation> results) {
        if (shell == null || shell.isDisposed()) return;

        if (results.isEmpty()) {
            MessageDialog.openInformation(shell, "Find All Declarations",
                    "No declarations found for '" + query + "'.\n\n"
                    + "Tip: use OpenJML > Index Project to index all source files first.");
            return;
        }

        ElementListSelectionDialog dlg = new ElementListSelectionDialog(shell,
                new LabelProvider() {
                    @Override
                    public String getText(Object element) {
                        if (!(element instanceof SymbolInformation si)) return "";
                        Location loc = si.getLocation();
                        String file = loc != null ? fileBaseName(loc.getUri()) : "?";
                        int line    = loc != null ? loc.getRange().getStart().getLine() + 1 : 0;
                        String cont = si.getContainerName();
                        return si.getName()
                                + (cont != null && !cont.isEmpty() ? " — " + cont : "")
                                + "  [" + file + ":" + line + "]";
                    }
                });
        dlg.setTitle("Find All Declarations");
        dlg.setMessage("Declarations matching '" + query + "' (" + results.size() + " found):");
        dlg.setElements(results.toArray());
        dlg.setMultipleSelection(false);
        if (dlg.open() != Window.OK) return;

        Object[] chosen = dlg.getResult();
        if (chosen == null || chosen.length == 0) return;

        SymbolInformation si = (SymbolInformation) chosen[0];
        Location loc = si.getLocation();
        if (loc != null) {
            LSPEclipseUtils.open(loc.getUri(), loc.getRange());
        }
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /** Returns the selection text if it is a valid Java identifier, else {@code null}. */
    private static String getSelectedIdentifier(IEditorPart editor) {
        if (editor == null) return null;
        var sel = editor.getSite().getSelectionProvider().getSelection();
        if (!(sel instanceof ITextSelection ts)) return null;
        String text = ts.getText().trim();
        return isValidIdentifier(text) ? text : null;
    }

    /** Returns {@code true} if {@code s} is a non-empty valid Java identifier. */
    private static boolean isValidIdentifier(String s) {
        if (s == null || s.isEmpty()) return false;
        if (!Character.isJavaIdentifierStart(s.charAt(0))) return false;
        for (int i = 1; i < s.length(); i++)
            if (!Character.isJavaIdentifierPart(s.charAt(i))) return false;
        return true;
    }

    /** Returns the project of the active editor's file, falling back to the first JML project. */
    private static IProject getActiveProject(IEditorPart editor) {
        if (editor != null) {
            var resource = org.eclipse.ui.ide.ResourceUtil.getResource(editor.getEditorInput());
            if (resource != null) return resource.getProject();
        }
        for (IProject p : ResourcesPlugin.getWorkspace().getRoot().getProjects()) {
            if (p.isOpen() && JmlNature.hasNature(p)) return p;
        }
        return null;
    }

    /** Extracts just the filename portion of a URI or path string. */
    private static String fileBaseName(String uri) {
        if (uri == null) return "?";
        int slash = Math.max(uri.lastIndexOf('/'), uri.lastIndexOf('\\'));
        return slash >= 0 ? uri.substring(slash + 1) : uri;
    }
}
