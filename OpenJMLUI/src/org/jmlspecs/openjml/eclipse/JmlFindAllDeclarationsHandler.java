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
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.window.Window;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.WorkspaceSymbol;
import org.eclipse.lsp4j.WorkspaceSymbolLocation;
import org.eclipse.lsp4j.WorkspaceSymbolParams;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.eclipse.ui.handlers.HandlerUtil;

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
 * <p><b>Project filtering:</b>
 * The project root is encoded into the {@code workspace/symbol} query string
 * as {@code "<projectRoot>\n<identifier>"}.  The server extracts the root and
 * filters its declaration index to files under that project.  This avoids any
 * client-side Gson dependency and uses the standard LSP wire path.
 *
 * <p><b>Coverage note:</b> The server's declaration index is populated as files
 * are opened and checked.  Use "Index Project" (OpenJML menu) to index all
 * source files in the project before searching, so that declarations in
 * unopened files are also found.
 */
public class JmlFindAllDeclarationsHandler extends AbstractHandler {

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
        scheduleSearch(shell, query, project);

        return null;
    }

    /**
     * Schedule a background search for {@code query} in {@code project} and
     * display the results (or a retry dialog) on the UI thread when done.
     */
    private static void scheduleSearch(Shell shell, String query, IProject project) {
        Job.create("Find All Declarations: " + query, (monitor) -> {
            List<SymbolInformation> results;
            try {
                results = queryDeclarations(query, project);
            } catch (Throwable t) {
                System.err.println("[FindAllDecl] Job body threw: " + t);
                t.printStackTrace(System.err);
                results = List.of();
            }
            final List<SymbolInformation> finalResults = results;
            Display.getDefault().asyncExec(() -> showResults(shell, query, project, finalResults));
            return Status.OK_STATUS;
        }).schedule();
    }

    // -----------------------------------------------------------------------
    // Server query
    // -----------------------------------------------------------------------

    private static List<SymbolInformation> queryDeclarations(String query, IProject project) {
        String projectRoot = (project != null && project.getLocation() != null)
                ? project.getLocation().toOSString() : null;
        System.err.println("[FindAllDecl] query=\"" + query + "\" projectRoot=" + projectRoot
                + " wrapper=" + (LspPartListener.cachedWrapper != null ? "present" : "null"));

        List<SymbolInformation> results = symbolsViaWrapper(
                LspPartListener.cachedWrapper, query, projectRoot);
        if (results != null) return results;

        System.err.println("[FindAllDecl] server not available — returning empty");
        return List.of();
    }

    /**
     * Send a {@code workspace/symbol} request to the language server via the
     * cached {@code LanguageServerWrapper}.
     *
     * <p>The project root is encoded into the query string as
     * {@code "<projectRoot>\n<identifier>"} so the server can filter its
     * declaration index to files under that project without requiring a custom
     * command or any Gson dependency on the client side.
     *
     * @return the symbol list on success, or {@code null} if the wrapper is
     *         unavailable or the call fails
     */
    private static List<SymbolInformation> symbolsViaWrapper(
            Object wrapper, String query, String projectRoot) {
        if (wrapper == null) {
            System.err.println("[FindAllDecl] symbolsViaWrapper: wrapper is null");
            return null;
        }
        System.err.println("[FindAllDecl] symbolsViaWrapper: wrapper class=" + wrapper.getClass().getName());
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
                System.err.println("[FindAllDecl] getServer() not found on wrapper hierarchy");
                return null;
            }

            Object serverFuture = getServer.invoke(wrapper);
            System.err.println("[FindAllDecl] getServer() returned: "
                    + (serverFuture != null ? serverFuture.getClass().getName() : "null"));
            org.eclipse.lsp4j.services.LanguageServer server = null;
            if (serverFuture instanceof java.util.concurrent.CompletableFuture<?> cf) {
                Object result = cf.get(5, TimeUnit.SECONDS);
                System.err.println("[FindAllDecl] CompletableFuture resolved: "
                        + (result != null ? result.getClass().getName() : "null"));
                if (result instanceof org.eclipse.lsp4j.services.LanguageServer ls) server = ls;
            } else if (serverFuture instanceof org.eclipse.lsp4j.services.LanguageServer ls) {
                server = ls;
            }
            if (server == null) {
                System.err.println("[FindAllDecl] could not obtain LanguageServer from wrapper");
                return null;
            }
            System.err.println("[FindAllDecl] LanguageServer obtained: " + server.getClass().getName());

            // Encode the project root into the query using a newline separator.
            // Java identifiers cannot contain newlines, so this is unambiguous.
            String encodedQuery = (projectRoot != null && !projectRoot.isEmpty())
                    ? projectRoot + "\n" + query : query;
            WorkspaceSymbolParams params = new WorkspaceSymbolParams(encodedQuery);
            System.err.println("[FindAllDecl] sending workspace/symbol, encodedQuery length="
                    + encodedQuery.length());

            var either = server.getWorkspaceService().symbol(params)
                    .get(15, TimeUnit.SECONDS);
            System.err.println("[FindAllDecl] symbol() returned: "
                    + (either != null ? "isLeft=" + either.isLeft() : "null"));

            List<SymbolInformation> symbols = eitherToList(either);
            System.err.println("[FindAllDecl] " + symbols.size() + " result(s) for query=\"" + query + "\""
                    + (projectRoot != null ? " root=\"" + projectRoot + "\"" : ""));
            return symbols;
        } catch (Throwable t) {
            System.err.println("[FindAllDecl] exception: " + t.getClass().getName() + ": " + t.getMessage());
            t.printStackTrace(System.err);
            return null;
        }
    }

    /**
     * Convert an LSP4J {@code workspace/symbol} response to a flat
     * {@code List<SymbolInformation>}, handling both the legacy left side
     * ({@code SymbolInformation[]}) and the LSP 3.17 right side
     * ({@code WorkspaceSymbol[]}).
     */
    private static List<SymbolInformation> eitherToList(
            Either<List<? extends SymbolInformation>,
                   List<? extends WorkspaceSymbol>> either) {
        if (either == null) return List.of();
        if (either.isLeft()) return new ArrayList<>(either.getLeft());
        // LSP 3.17+: server responded with WorkspaceSymbol (right side).
        List<SymbolInformation> result = new ArrayList<>();
        for (WorkspaceSymbol ws : either.getRight()) {
            Location loc;
            Either<Location, WorkspaceSymbolLocation> wloc = ws.getLocation();
            if (wloc != null && wloc.isLeft()) {
                loc = wloc.getLeft();
            } else if (wloc != null && wloc.isRight()) {
                loc = new Location(wloc.getRight().getUri(),
                        new org.eclipse.lsp4j.Range(
                                new org.eclipse.lsp4j.Position(0, 0),
                                new org.eclipse.lsp4j.Position(0, 0)));
            } else {
                loc = null;
            }
            SymbolInformation si = new SymbolInformation(ws.getName(), ws.getKind(), loc);
            si.setContainerName(ws.getContainerName());
            result.add(si);
        }
        return result;
    }

    // -----------------------------------------------------------------------
    // Result presentation
    // -----------------------------------------------------------------------

    private static void showResults(Shell shell, String query, IProject project,
                                    List<SymbolInformation> results) {
        if (shell == null || shell.isDisposed()) return;

        if (results.isEmpty()) {
            InputDialog dlg = new InputDialog(shell,
                    "Find All Declarations",
                    "No declarations found for '" + query + "'.\n"
                    + "Tip: use OpenJML \u25b8 Index Project first.\n\n"
                    + "Search again with a different identifier:",
                    query,
                    input -> isValidIdentifier(input.trim())
                            ? null : "Enter a valid Java identifier");
            if (dlg.open() != Window.OK) return;
            String newQuery = dlg.getValue().trim();
            if (newQuery.isEmpty()) return;
            scheduleSearch(shell, newQuery, project);
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
