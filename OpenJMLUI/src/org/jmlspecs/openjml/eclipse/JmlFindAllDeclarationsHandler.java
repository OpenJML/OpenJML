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
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.window.Window;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.Range;
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
        final org.eclipse.jface.text.IDocument doc = getActiveDocument(editor);
        final IProject project = getActiveProject(editor);

        // Step 2: query the server on a background thread, then show results.
        Job.create("Find All Declarations: " + query, (monitor) -> {
            List<SymbolInformation> results = queryDeclarations(query, doc, project);
            Display.getDefault().asyncExec(() -> showResults(shell, query, results));
            return Status.OK_STATUS;
        }).schedule();

        return null;
    }

    // -----------------------------------------------------------------------
    // Server query
    // -----------------------------------------------------------------------

    private static List<SymbolInformation> queryDeclarations(
            String query,
            org.eclipse.jface.text.IDocument doc,
            IProject project) {
        WorkspaceSymbolParams params = new WorkspaceSymbolParams(query);

        // Prefer the cached wrapper: the server is connected via LspPartListener's
        // custom mechanism, not through LSP4E's content-type registry, so
        // LanguageServers.forDocument/forProject won't find it.
        List<SymbolInformation> viaWrapper = symbolsViaWrapper(
                LspPartListener.cachedWrapper, params);
        if (viaWrapper != null) {
            return filterByProject(viaWrapper, project);
        }

        // Fallback: let LSP4E route the request (works when the server was started
        // through the standard content-type mechanism rather than LspPartListener).
        try {
            var future = doc != null
                    ? LanguageServers.forDocument(doc)
                            .computeFirst(s -> s.getWorkspaceService()
                                    .symbol(params).thenApply(JmlFindAllDeclarationsHandler::eitherToList))
                    : LanguageServers.forProject(project)
                            .computeFirst(s -> s.getWorkspaceService()
                                    .symbol(params).thenApply(JmlFindAllDeclarationsHandler::eitherToList));
            var opt = future.get(15, TimeUnit.SECONDS);
            List<SymbolInformation> results =
                    (opt != null && opt.isPresent()) ? opt.get() : List.of();
            return filterByProject(results, project);
        } catch (Exception e) {
            Console.log("Find All Declarations: server query failed: " + e.getMessage());
            return List.of();
        }
    }

    /**
     * Send a {@code workspace/symbol} request to the language server via the
     * cached {@code LanguageServerWrapper} (same reflection approach used by
     * {@link LspCommandHandler#sendViaWrapper}).
     *
     * @return the symbol list on success, or {@code null} if the wrapper is
     *         unavailable or the call fails (caller should fall back)
     */
    private static List<SymbolInformation> symbolsViaWrapper(
            Object wrapper, WorkspaceSymbolParams params) {
        if (wrapper == null) return null;
        try {
            java.lang.reflect.Method getServer = null;
            for (Class<?> c = wrapper.getClass();
                    c != null && c != Object.class; c = c.getSuperclass()) {
                try {
                    getServer = c.getDeclaredMethod("getServer");
                    getServer.setAccessible(true);
                    break;
                } catch (NoSuchMethodException ignored) {}
            }
            if (getServer == null) return null;

            Object serverFuture = getServer.invoke(wrapper);
            org.eclipse.lsp4j.services.LanguageServer server = null;
            if (serverFuture instanceof java.util.concurrent.CompletableFuture<?> cf) {
                Object result = cf.get(5, TimeUnit.SECONDS);
                if (result instanceof org.eclipse.lsp4j.services.LanguageServer ls) server = ls;
            } else if (serverFuture instanceof org.eclipse.lsp4j.services.LanguageServer ls) {
                server = ls;
            }
            if (server == null) return null;

            var either = server.getWorkspaceService().symbol(params)
                    .get(15, TimeUnit.SECONDS);
            return eitherToList(either);
        } catch (Throwable t) {
            Console.log("Find All Declarations: symbolsViaWrapper failed: " + t.getMessage());
            return null;
        }
    }

    /**
     * Filter {@code results} to only include declarations whose URI falls
     * under the given Eclipse project's location.  When {@code project} is
     * {@code null}, all results are returned.
     *
     * <p>URI comparison is done via OS path (to avoid {@code file:/} vs
     * {@code file:///} format differences between Eclipse and the LSP server).
     */
    private static List<SymbolInformation> filterByProject(
            List<SymbolInformation> results, IProject project) {
        // Log every result the server returned so path-comparison issues are visible.
        Console.log("[FindAllDeclarations] " + results.size()
                + " result(s) from server (project=" + (project != null ? project.getName() : "null") + "):");
        for (SymbolInformation si : results) {
            Location l = si.getLocation();
            Console.log("[FindAllDeclarations]   " + si.getName()
                    + " @ " + (l != null ? l.getUri() : "(no location)"));
        }

        if (project == null || results.isEmpty()) return results;
        org.eclipse.core.runtime.IPath loc = project.getLocation();
        if (loc == null) return results;

        // Resolve the project root to its canonical path so that macOS symlinks
        // (/Users → /private/Users) don't cause mismatches with URI paths from
        // the server (which uses the logical path).
        java.nio.file.Path projectRoot;
        try {
            projectRoot = java.nio.file.Path.of(loc.toOSString()).toRealPath();
        } catch (java.io.IOException e) {
            projectRoot = java.nio.file.Path.of(loc.toOSString()).normalize();
        }
        final java.nio.file.Path root = projectRoot;
        Console.log("[FindAllDeclarations] project root (real): \"" + root + "\"");

        List<SymbolInformation> filtered = results.stream().filter(si -> {
            Location l = si.getLocation();
            if (l == null) return false;
            try {
                String rawPath = java.net.URI.create(l.getUri()).getPath();
                if (rawPath == null) return false;
                java.nio.file.Path filePath;
                try {
                    filePath = java.nio.file.Path.of(rawPath).toRealPath();
                } catch (java.io.IOException e) {
                    filePath = java.nio.file.Path.of(rawPath).normalize();
                }
                boolean keep = filePath.startsWith(root);
                if (!keep)
                    Console.log("[FindAllDeclarations]   DROPPED (no prefix match): "
                            + si.getName() + " real path=" + filePath);
                return keep;
            } catch (Exception e) {
                Console.log("[FindAllDeclarations]   DROPPED (exception): "
                        + si.getName() + " err=" + e);
                return false;
            }
        }).collect(java.util.stream.Collectors.toList());
        Console.log("[FindAllDeclarations] kept=" + filtered.size() + " after project filter");
        return filtered;
    }

    private static List<SymbolInformation> eitherToList(
            Either<List<? extends SymbolInformation>,
                   List<? extends org.eclipse.lsp4j.WorkspaceSymbol>> either) {
        if (either == null) return List.of();
        if (either.isLeft()) return new ArrayList<>(either.getLeft());
        // LSP 3.17+: server responded with WorkspaceSymbol (right side).
        // Convert to SymbolInformation so the rest of the handler is uniform.
        List<SymbolInformation> result = new ArrayList<>();
        for (WorkspaceSymbol ws : either.getRight()) {
            Location loc;
            Either<Location, WorkspaceSymbolLocation> wloc = ws.getLocation();
            if (wloc != null && wloc.isLeft()) {
                loc = wloc.getLeft();
            } else if (wloc != null && wloc.isRight()) {
                // Only URI available — create a Location with a zero range.
                loc = new Location(wloc.getRight().getUri(),
                        new Range(new Position(0, 0), new Position(0, 0)));
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

    /** Returns the open {@link org.eclipse.jface.text.IDocument} for the active editor, or {@code null}. */
    private static org.eclipse.jface.text.IDocument getActiveDocument(IEditorPart editor) {
        if (editor == null) return null;
        var resource = org.eclipse.ui.ide.ResourceUtil.getResource(editor.getEditorInput());
        return resource != null ? LSPEclipseUtils.getDocument(resource) : null;
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
