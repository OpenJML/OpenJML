/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
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
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * Handles the {@code org.openjml.eclipse.commands.findAllDeclarations} command.
 *
 * <p>Opens a search dialog pre-populated with any selected text, lets the user
 * adjust the query and matching options, then queries the OpenJML language
 * server's declaration index and presents the results in a selection dialog.
 * Double-clicking (or pressing OK) navigates to the selected declaration.
 *
 * <p><b>Matching model:</b>
 * The server performs a case-insensitive substring match against all identifier
 * names in its declaration index.  The Eclipse client applies an optional
 * additional filter based on the "Case insensitive" and "Full word" toggles:
 * <ul>
 *   <li><b>Case insensitive + partial</b> (defaults): use server results as-is.</li>
 *   <li><b>Case sensitive + partial</b>: retain only names that contain the query
 *       with the original casing.</li>
 *   <li><b>Full word</b>: retain only names whose entire text equals the query
 *       (case-insensitively or case-sensitively depending on the other toggle).</li>
 * </ul>
 *
 * <p><b>Project filtering:</b>
 * The project root of the active editor is encoded into the {@code workspace/symbol}
 * query string as {@code "<projectRoot>\n<identifier>"}.  The server extracts the
 * root and filters its declaration index to files under that project.
 *
 * <p><b>Persistent state:</b> The "Case insensitive" and "Full word" toggle values
 * are remembered for the lifetime of the Eclipse session (static fields).
 */
public class JmlFindAllDeclarationsHandler extends AbstractHandler {

    /** Session-persistent toggle state — remembered until Eclipse exits. */
    private static boolean lastCaseInsensitive = true;
    private static boolean lastFullWord        = false;

    // -----------------------------------------------------------------------
    // Dialog
    // -----------------------------------------------------------------------

    /**
     * Search dialog with a query text field and two option toggles.
     * Results are available via {@link #query}, {@link #caseInsensitive},
     * and {@link #fullWord} after {@code open()} returns {@link Window#OK}.
     */
    private static class FindDialog extends Dialog {

        private final String  initialQuery;
        private final boolean initCaseInsensitive;
        private final boolean initFullWord;

        private Text   queryText;
        private Button caseInsensitiveCheck;
        private Button fullWordCheck;

        String  query;
        boolean caseInsensitive;
        boolean fullWord;

        FindDialog(Shell parent, String initialQuery,
                   boolean initCaseInsensitive, boolean initFullWord) {
            super(parent);
            this.initialQuery        = initialQuery != null ? initialQuery : "";
            this.initCaseInsensitive = initCaseInsensitive;
            this.initFullWord        = initFullWord;
        }

        @Override
        protected void configureShell(Shell shell) {
            super.configureShell(shell);
            shell.setText("Find All Declarations");
        }

        @Override
        protected Control createDialogArea(Composite parent) {
            Composite area = (Composite) super.createDialogArea(parent);

            Label label = new Label(area, SWT.NONE);
            label.setText("Identifier (substring, case-insensitive by default):");

            queryText = new Text(area, SWT.SINGLE | SWT.BORDER);
            queryText.setText(initialQuery);
            queryText.selectAll();
            GridData gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
            gd.widthHint = 320;
            queryText.setLayoutData(gd);

            caseInsensitiveCheck = new Button(area, SWT.CHECK);
            caseInsensitiveCheck.setText("Case insensitive");
            caseInsensitiveCheck.setSelection(initCaseInsensitive);

            fullWordCheck = new Button(area, SWT.CHECK);
            fullWordCheck.setText("Full word");
            fullWordCheck.setSelection(initFullWord);

            return area;
        }

        @Override
        protected void createButtonsForButtonBar(Composite parent) {
            createButton(parent, IDialogConstants.OK_ID, "Match", true);
            createButton(parent, IDialogConstants.CANCEL_ID, IDialogConstants.CANCEL_LABEL, false);
        }

        @Override
        protected void okPressed() {
            query           = queryText.getText().trim();
            caseInsensitive = caseInsensitiveCheck.getSelection();
            fullWord        = fullWordCheck.getSelection();
            super.okPressed();
        }
    }

    // -----------------------------------------------------------------------
    // Handler entry point
    // -----------------------------------------------------------------------

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {

        Shell     shell  = HandlerUtil.getActiveShell(event);
        IEditorPart editor = HandlerUtil.getActiveEditor(event);

        String initialQuery = getSelectedText(editor);

        FindDialog dlg = new FindDialog(shell, initialQuery, lastCaseInsensitive, lastFullWord);
        if (dlg.open() != Window.OK) return null;
        String query = dlg.query;
        if (query.isEmpty()) return null;
        lastCaseInsensitive = dlg.caseInsensitive;
        lastFullWord        = dlg.fullWord;

        scheduleSearch(shell, query, getActiveProject(editor),
                dlg.caseInsensitive, dlg.fullWord);
        return null;
    }

    // -----------------------------------------------------------------------
    // Background search
    // -----------------------------------------------------------------------

    private static void scheduleSearch(Shell shell, String query, IProject project,
                                       boolean caseInsensitive, boolean fullWord) {
        Job.create("Find All Declarations: " + query, (monitor) -> {
            List<SymbolInformation> results;
            try {
                results = queryDeclarations(query, project);
                results = applyClientFilter(results, query, caseInsensitive, fullWord);
            } catch (Throwable t) {
                System.err.println("[OpenJML] find declarations job error: " + t);
                t.printStackTrace(System.err);
                results = List.of();
            }
            final List<SymbolInformation> finalResults = results;
            Display.getDefault().asyncExec(
                    () -> showResults(shell, query, project,
                                      caseInsensitive, fullWord, finalResults));
            return Status.OK_STATUS;
        }).schedule();
    }

    // -----------------------------------------------------------------------
    // Server query
    // -----------------------------------------------------------------------

    private static List<SymbolInformation> queryDeclarations(String query, IProject project) {
        String projectRoot = (project != null && project.getLocation() != null)
                ? project.getLocation().toOSString() : null;

        List<SymbolInformation> results = symbolsViaWrapper(
                LspPartListener.cachedWrapper, query, projectRoot);
        if (results != null) return results;

        System.err.println("[OpenJML] find declarations: server not available");
        return List.of();
    }

    /**
     * Send a {@code workspace/symbol} request to the language server.
     *
     * <p>The project root is encoded into the query string as
     * {@code "<projectRoot>\n<identifier>"} so the server can filter its
     * declaration index to files under that project without requiring a custom
     * command or any Gson dependency on the client side.
     */
    private static List<SymbolInformation> symbolsViaWrapper(
            Object wrapper, String query, String projectRoot) {
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

            String encodedQuery = (projectRoot != null && !projectRoot.isEmpty())
                    ? projectRoot + "\n" + query : query;
            WorkspaceSymbolParams params = new WorkspaceSymbolParams(encodedQuery);

            var either = server.getWorkspaceService().symbol(params)
                    .get(15, TimeUnit.SECONDS);

            List<SymbolInformation> symbols = eitherToList(either);
            System.err.println("[OpenJML] find declarations: query=\"" + query
                    + "\" -> " + symbols.size() + " result(s) (before client filter)");
            return symbols;
        } catch (Throwable t) {
            System.err.println("[OpenJML] find declarations exception: "
                    + t.getClass().getName() + ": " + t.getMessage());
            return null;
        }
    }

    private static List<SymbolInformation> eitherToList(
            Either<List<? extends SymbolInformation>,
                   List<? extends WorkspaceSymbol>> either) {
        if (either == null) return List.of();
        if (either.isLeft()) return new ArrayList<>(either.getLeft());
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
    // Client-side filter
    // -----------------------------------------------------------------------

    /**
     * Apply the case/word toggles as a post-filter on the server's results.
     *
     * <p>The server always returns case-insensitive substring matches, so:
     * <ul>
     *   <li>Case-insensitive + partial: no additional filtering needed.</li>
     *   <li>Case-sensitive + partial: retain only names that contain the query
     *       with original casing.</li>
     *   <li>Full word: retain only names that exactly equal the query (respecting
     *       the case toggle).</li>
     * </ul>
     */
    private static List<SymbolInformation> applyClientFilter(
            List<SymbolInformation> results, String query,
            boolean caseInsensitive, boolean fullWord) {
        if (results.isEmpty() || query.isEmpty()) return results;
        // Case-insensitive partial is what the server already returns — no extra work.
        if (caseInsensitive && !fullWord) return results;
        return results.stream().filter(si -> {
            String name = si.getName();
            String n = caseInsensitive ? name.toLowerCase() : name;
            String q = caseInsensitive ? query.toLowerCase() : query;
            return fullWord ? n.equals(q) : n.contains(q);
        }).collect(Collectors.toList());
    }

    // -----------------------------------------------------------------------
    // Result presentation
    // -----------------------------------------------------------------------

    private static void showResults(Shell shell, String query, IProject project,
                                    boolean caseInsensitive, boolean fullWord,
                                    List<SymbolInformation> results) {
        if (shell == null || shell.isDisposed()) return;

        if (results.isEmpty()) {
            boolean retry = MessageDialog.openQuestion(shell,
                    "Find All Declarations",
                    "No declarations found for '" + query + "'.\n"
                    + "Tip: use OpenJML \u25b8 Index Project first.\n\n"
                    + "Search again?");
            if (!retry) return;
            FindDialog dlg = new FindDialog(shell, query, caseInsensitive, fullWord);
            if (dlg.open() != Window.OK) return;
            String newQuery = dlg.query;
            if (newQuery.isEmpty()) return;
            lastCaseInsensitive = dlg.caseInsensitive;
            lastFullWord        = dlg.fullWord;
            scheduleSearch(shell, newQuery, project, dlg.caseInsensitive, dlg.fullWord);
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
                                + (cont != null && !cont.isEmpty() ? " \u2014 " + cont : "")
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

    /** Returns the current editor selection text (trimmed), or empty string. */
    private static String getSelectedText(IEditorPart editor) {
        if (editor == null) return "";
        var sel = editor.getSite().getSelectionProvider().getSelection();
        if (!(sel instanceof ITextSelection ts)) return "";
        return ts.getText().trim();
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
