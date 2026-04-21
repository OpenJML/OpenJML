/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.lsp4e.LSPEclipseUtils;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.SymbolKind;
import org.eclipse.lsp4j.WorkspaceSymbolParams;
import org.eclipse.search.ui.ISearchQuery;
import org.eclipse.search.ui.ISearchResult;
import org.eclipse.search.ui.NewSearchUI;
import org.eclipse.search.ui.text.AbstractTextSearchResult;
import org.eclipse.search.ui.text.IEditorMatchAdapter;
import org.eclipse.search.ui.text.IFileMatchAdapter;
import org.eclipse.search.ui.text.Match;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * Handles the {@code org.openjml.eclipse.commands.findAllDeclarations} command.
 *
 * <p>Opens a search dialog pre-populated with any selected text, lets the user
 * adjust the query and matching options, then queries the OpenJML language
 * server's declaration index and displays the results in the Eclipse Search view.
 *
 * <p><b>Matching model:</b>
 * The server performs a case-insensitive substring match against all identifier
 * names in its declaration index.  The Eclipse client applies an optional
 * additional filter based on the "Case sensitive" and "Full word" toggles:
 * <ul>
 *   <li><b>Case insensitive + partial</b> (defaults): use server results as-is.</li>
 *   <li><b>Case sensitive + partial</b>: retain only names that contain the query
 *       with the original casing.</li>
 *   <li><b>Full word</b>: retain only names whose entire text equals the query
 *       (case-insensitively or case-sensitively depending on the other toggle).</li>
 * </ul>
 *
 * <p><b>Project filtering:</b>
 * The Eclipse project name is passed as the {@code projectId} argument to the
 * server, which filters the declaration index to files belonging to that project.
 *
 * <p><b>Persistent state:</b> The "Case sensitive" and "Full word" toggle values
 * are remembered for the lifetime of the Eclipse session (static fields).
 */
public class JmlFindAllDeclarationsHandler extends AbstractHandler {

    /** Session-persistent toggle state — remembered until Eclipse exits. */
    private static boolean lastCaseSensitive = false;
    private static boolean lastFullWord      = false;

    // -----------------------------------------------------------------------
    // Dialog
    // -----------------------------------------------------------------------

    /**
     * Search dialog with a query text field and two option toggles.
     * Results are available via {@link #query}, {@link #caseSensitive},
     * and {@link #fullWord} after {@code open()} returns {@link Window#OK}.
     */
    private static class FindDialog extends Dialog {

        private final String  statusMessage;
        private final String  initialQuery;
        private final boolean initCaseSensitive;
        private final boolean initFullWord;

        private Text   queryText;
        private Button caseSensitiveCheck;
        private Button fullWordCheck;

        String  query;
        boolean caseSensitive;
        boolean fullWord;

        FindDialog(Shell parent, String initialQuery,
                   boolean initCaseSensitive, boolean initFullWord) {
            this(parent, null, initialQuery, initCaseSensitive, initFullWord);
        }

        FindDialog(Shell parent, String statusMessage, String initialQuery,
                   boolean initCaseSensitive, boolean initFullWord) {
            super(parent);
            this.statusMessage    = statusMessage;
            this.initialQuery     = initialQuery != null ? initialQuery : "";
            this.initCaseSensitive = initCaseSensitive;
            this.initFullWord     = initFullWord;
        }

        @Override
        protected void configureShell(Shell shell) {
            super.configureShell(shell);
            shell.setText("Find All Declarations");
        }

        @Override
        protected Control createDialogArea(Composite parent) {
            Composite area = (Composite) super.createDialogArea(parent);

            if (statusMessage != null && !statusMessage.isEmpty()) {
                Label msg = new Label(area, SWT.WRAP);
                msg.setText(statusMessage);
                GridData mgd = new GridData(SWT.FILL, SWT.CENTER, true, false);
                mgd.widthHint = 320;
                msg.setLayoutData(mgd);
            }

            Label label = new Label(area, SWT.NONE);
            label.setText("Identifier (substring match):");

            queryText = new Text(area, SWT.SINGLE | SWT.BORDER);
            queryText.setText(initialQuery);
            queryText.selectAll();
            GridData gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
            gd.widthHint = 320;
            queryText.setLayoutData(gd);

            caseSensitiveCheck = new Button(area, SWT.CHECK);
            caseSensitiveCheck.setText("Case sensitive");
            caseSensitiveCheck.setSelection(initCaseSensitive);

            fullWordCheck = new Button(area, SWT.CHECK);
            fullWordCheck.setText("Full word");
            fullWordCheck.setSelection(initFullWord);

            return area;
        }

        @Override
        protected void createButtonsForButtonBar(Composite parent) {
            createButton(parent, IDialogConstants.OK_ID, "Search", true);
            createButton(parent, IDialogConstants.CANCEL_ID, IDialogConstants.CANCEL_LABEL, false);
        }

        @Override
        protected void okPressed() {
            query         = queryText.getText().trim();
            caseSensitive = caseSensitiveCheck.getSelection();
            fullWord      = fullWordCheck.getSelection();
            super.okPressed();
        }
    }

    // -----------------------------------------------------------------------
    // Handler entry point
    // -----------------------------------------------------------------------

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        Console.show();

        Shell      shell  = HandlerUtil.getActiveShell(event);
        IEditorPart editor = HandlerUtil.getActiveEditor(event);

        String initialQuery = getSelectedText(editor);

        FindDialog dlg = new FindDialog(shell, initialQuery, lastCaseSensitive, lastFullWord);
        if (dlg.open() != Window.OK) return null;
        String query = dlg.query;
        if (query.isEmpty()) return null;
        lastCaseSensitive = dlg.caseSensitive;
        lastFullWord      = dlg.fullWord;

        IProject project = getActiveProject(editor);
        DeclarationSearchQuery searchQuery = new DeclarationSearchQuery(
                query, dlg.caseSensitive, dlg.fullWord, project, shell);
        NewSearchUI.runQueryInBackground(searchQuery);
        return null;
    }

    // -----------------------------------------------------------------------
    // Search query (runs in background, populates Search view)
    // -----------------------------------------------------------------------

    private static final class DeclarationSearchQuery implements ISearchQuery {

        private final String  query;
        private final boolean caseSensitive;
        private final boolean fullWord;
        private final IProject project;
        private final Shell   shell;
        private final DeclarationSearchResult result;

        DeclarationSearchQuery(String query, boolean caseSensitive,
                               boolean fullWord, IProject project, Shell shell) {
            this.query         = query;
            this.caseSensitive = caseSensitive;
            this.fullWord      = fullWord;
            this.project       = project;
            this.shell         = shell;
            this.result        = new DeclarationSearchResult(this);
        }

        @Override
        public String getLabel() {
            return "OpenJML declarations matching '" + query + "'";
        }

        @Override
        public boolean canRerun()           { return true; }
        @Override
        public boolean canRunInBackground() { return true; }

        @Override
        public ISearchResult getSearchResult() { return result; }

        @Override
        public IStatus run(IProgressMonitor monitor) {
            result.removeAll();
            List<SymbolInformation> symbols;
            try {
                symbols = queryDeclarations(query, project);
                symbols = applyClientFilter(symbols, query, caseSensitive, fullWord);
            } catch (Throwable t) {
                Console.log("Find declarations job error: " + t);
                return Status.OK_STATUS;
            }
            for (SymbolInformation si : symbols) {
                if (monitor != null && monitor.isCanceled()) break;
                Location loc = si.getLocation();
                if (loc == null) continue;
                IFile file = uriToIFile(loc.getUri());
                if (file == null) continue;
                int[] offsetLen = rangeToOffsetLen(file, loc);
                result.addMatch(new DeclarationMatch(file, offsetLen[0], offsetLen[1],
                        si.getName(), si.getContainerName(), si.getKind()));
            }
            if (result.getMatchCount() == 0 && shell != null) {
                org.eclipse.swt.widgets.Display.getDefault().asyncExec(() -> {
                    if (shell.isDisposed()) return;
                    FindDialog dlg = new FindDialog(shell,
                            "No results for '" + query + "' — edit and retry.",
                            query, caseSensitive, fullWord);
                    if (dlg.open() != Window.OK) return;
                    String newQuery = dlg.query;
                    if (newQuery.isEmpty()) return;
                    lastCaseSensitive = dlg.caseSensitive;
                    lastFullWord      = dlg.fullWord;
                    DeclarationSearchQuery next = new DeclarationSearchQuery(
                            newQuery, dlg.caseSensitive, dlg.fullWord, project, shell);
                    NewSearchUI.runQueryInBackground(next);
                });
            }
            return Status.OK_STATUS;
        }
    }

    // -----------------------------------------------------------------------
    // DeclarationMatch — carries symbol metadata for the result page label
    // -----------------------------------------------------------------------

    static final class DeclarationMatch extends Match {
        final String symbolName;
        final String containerName;
        final String kindLabel;

        DeclarationMatch(IFile file, int offset, int length,
                         String symbolName, String containerName, SymbolKind kind) {
            super(file, offset, length);
            this.symbolName    = symbolName != null ? symbolName : "";
            this.containerName = containerName != null ? containerName : "";
            this.kindLabel     = kindName(kind);
        }

        private static String kindName(SymbolKind k) {
            if (k == null) return "";
            return switch (k) {
                case Class       -> "class";
                case Interface   -> "interface";
                case Enum        -> "enum";
                case Method      -> "method";
                case Field       -> "field";
                case Constructor -> "constructor";
                default          -> k.name().toLowerCase();
            };
        }
    }

    // -----------------------------------------------------------------------
    // Search result (holds Match objects for the Search view)
    // -----------------------------------------------------------------------

    static final class DeclarationSearchResult extends AbstractTextSearchResult {

        private final DeclarationSearchQuery query;

        DeclarationSearchResult(DeclarationSearchQuery query) {
            this.query = query;
        }

        @Override
        public String getLabel() {
            int n = getMatchCount();
            return n + " declaration" + (n == 1 ? "" : "s") + " matching '"
                    + query.query + "'";
        }

        @Override
        public String getTooltip()                { return getLabel(); }
        @Override
        public org.eclipse.jface.resource.ImageDescriptor getImageDescriptor() { return null; }
        @Override
        public ISearchQuery getQuery()            { return query; }
        @Override
        public IEditorMatchAdapter getEditorMatchAdapter() { return null; }
        @Override
        public IFileMatchAdapter getFileMatchAdapter() { return FILE_MATCH_ADAPTER; }
    }

    private static final IFileMatchAdapter FILE_MATCH_ADAPTER = new IFileMatchAdapter() {
        @Override
        public Match[] computeContainedMatches(AbstractTextSearchResult result, IFile file) {
            return result.getMatches(file);
        }
        @Override
        public IFile getFile(Object element) {
            return element instanceof IFile f ? f : null;
        }
    };

    // -----------------------------------------------------------------------
    // Server query
    // -----------------------------------------------------------------------

    private static List<SymbolInformation> queryDeclarations(String query, IProject project) {
        String projectId = (project != null) ? project.getName() : null;
        List<SymbolInformation> results = symbolsViaWrapper(
                LspPartListener.cachedWrapper, query, projectId);
        if (results == null) {
            Console.log("Find declarations: OpenJML server not available");
            return List.of();
        }
        return results;
    }

    /**
     * Send a {@code workspace/symbol} request to the language server with the
     * project ID encoded in the query string as {@code "<projectId>\n<query>"}.
     */
    private static List<SymbolInformation> symbolsViaWrapper(
            Object wrapper, String query, String projectId) {
        if (wrapper == null) {
            Console.log("OpenJML: Find declarations — server not available");
            return null;
        }
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
            if (getServer == null) {
                Console.log("OpenJML: Find declarations — getServer() not found on "
                        + wrapper.getClass().getName());
                return null;
            }

            Object serverFuture = getServer.invoke(wrapper);
            org.eclipse.lsp4j.services.LanguageServer server = null;
            if (serverFuture instanceof java.util.concurrent.CompletableFuture<?> cf) {
                Object res = cf.get(5, TimeUnit.SECONDS);
                if (res instanceof org.eclipse.lsp4j.services.LanguageServer ls) server = ls;
            } else if (serverFuture instanceof org.eclipse.lsp4j.services.LanguageServer ls) {
                server = ls;
            }
            if (server == null) {
                Console.log("OpenJML: Find declarations — server not ready");
                return null;
            }

            String encodedQuery = (projectId != null && !projectId.isEmpty())
                    ? projectId + "\n" + query : query;
            WorkspaceSymbolParams wsParams = new WorkspaceSymbolParams(encodedQuery);
            Object wsRaw = server.getWorkspaceService().symbol(wsParams)
                    .get(15, TimeUnit.SECONDS);

            Object listObj = wsRaw;
            if (wsRaw instanceof org.eclipse.lsp4j.jsonrpc.messages.Either<?,?> either) {
                listObj = either.isLeft() ? either.getLeft() : either.getRight();
            }

            return parseSymbolList(listObj);
        } catch (Throwable t) {
            Console.log("OpenJML: Find declarations exception: " + t);
            t.printStackTrace();
            return null;
        }
    }

    /**
     * Deserialize the raw {@code workspace/symbol} result into a typed list.
     *
     * <p>LSP4j may deliver the response as typed {@code WorkspaceSymbol} objects
     * (when the response is processed within the same JVM), or as a {@code JsonArray},
     * or as a {@code List<Map>} for cross-process JSON-RPC deserialization.
     */
    private static List<SymbolInformation> parseSymbolList(Object raw) {
        List<SymbolInformation> result = new ArrayList<>();
        if (raw == null) return result;
        if (raw instanceof JsonArray arr) {
            for (JsonElement el : arr) {
                if (!el.isJsonObject()) continue;
                JsonObject obj = el.getAsJsonObject();
                String name = jsonStr(obj, "name");
                SymbolKind kind = SymbolKind.forValue(jsonInt(obj, "kind", 13));
                String container = jsonStr(obj, "containerName");
                Location loc = jsonLocation(obj.get("location"));
                SymbolInformation si = new SymbolInformation(name != null ? name : "", kind, loc);
                si.setContainerName(container);
                result.add(si);
            }
        } else if (raw instanceof List<?> list) {
            for (Object el : list) {
                if (el instanceof org.eclipse.lsp4j.WorkspaceSymbol ws) {
                    String name = ws.getName();
                    SymbolKind kind = ws.getKind();
                    String container = ws.getContainerName();
                    Location loc = null;
                    var locEither = ws.getLocation();
                    if (locEither != null) {
                        if (locEither.isLeft()) {
                            loc = locEither.getLeft();
                        } else if (locEither.getRight() != null) {
                            String uri = locEither.getRight().getUri();
                            loc = new Location(uri, new org.eclipse.lsp4j.Range(
                                    new org.eclipse.lsp4j.Position(0, 0),
                                    new org.eclipse.lsp4j.Position(0, 0)));
                        }
                    }
                    SymbolInformation si = new SymbolInformation(name != null ? name : "", kind, loc);
                    si.setContainerName(container);
                    result.add(si);
                } else if (el instanceof java.util.Map<?,?> obj) {
                    String name = mapStr(obj, "name");
                    SymbolKind kind = SymbolKind.forValue(mapInt(obj, "kind", 13));
                    String container = mapStr(obj, "containerName");
                    Location loc = null;
                    Object locRaw = obj.get("location");
                    if (locRaw instanceof java.util.Map<?,?> locMap) {
                        String uri = mapStr(locMap, "uri");
                        if (uri != null) {
                            Object rangeRaw = locMap.get("range");
                            org.eclipse.lsp4j.Range range = parseRangeMap(
                                    rangeRaw instanceof java.util.Map<?,?> rm ? rm : null);
                            loc = new Location(uri, range);
                        }
                    }
                    SymbolInformation si = new SymbolInformation(name != null ? name : "", kind, loc);
                    si.setContainerName(container);
                    result.add(si);
                }
            }
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
     *   <li>Case-insensitive partial: no additional filtering needed.</li>
     *   <li>Case-sensitive partial: retain only names that contain the query
     *       with the original casing.</li>
     *   <li>Full word: retain only names that exactly equal the query (respecting
     *       the case-sensitive toggle).</li>
     * </ul>
     */
    private static List<SymbolInformation> applyClientFilter(
            List<SymbolInformation> results, String query,
            boolean caseSensitive, boolean fullWord) {
        if (results.isEmpty() || query.isEmpty()) return results;
        if (!caseSensitive && !fullWord) return results;
        List<SymbolInformation> filtered = results.stream().filter(si -> {
            String name = si.getName();
            String n = caseSensitive ? name : name.toLowerCase();
            String q = caseSensitive ? query : query.toLowerCase();
            return fullWord ? n.equals(q) : n.contains(q);
        }).collect(Collectors.toList());
        return filtered;
    }

    // -----------------------------------------------------------------------
    // URI / IFile / offset helpers
    // -----------------------------------------------------------------------

    /** Resolve a file URI to an {@link IFile} in the workspace, or {@code null}. */
    private static IFile uriToIFile(String uri) {
        if (uri == null) return null;
        try {
            java.net.URI jUri = java.net.URI.create(uri);
            IFile[] files = ResourcesPlugin.getWorkspace().getRoot().findFilesForLocationURI(jUri);
            return files.length > 0 ? files[0] : null;
        } catch (Exception e) {
            return null;
        }
    }

    /**
     * Convert an LSP {@link Location} (line/character range) to a
     * {@code [charOffset, length]} pair within the file content.
     *
     * <p>Returns {@code [0, 0]} if the file cannot be read.
     */
    private static int[] rangeToOffsetLen(IFile file, Location loc) {
        if (loc == null) return new int[]{0, 0};
        var range = loc.getRange();
        if (range == null) return new int[]{0, 0};
        try {
            String content = new String(file.getContents().readAllBytes(),
                    file.getCharset());
            int startLine = range.getStart().getLine();
            int startChar = range.getStart().getCharacter();
            int endLine   = range.getEnd().getLine();
            int endChar   = range.getEnd().getCharacter();
            int offset = lineCharToOffset(content, startLine, startChar);
            int end    = lineCharToOffset(content, endLine,   endChar);
            return new int[]{offset, Math.max(0, end - offset)};
        } catch (Exception e) {
            return new int[]{0, 0};
        }
    }

    private static int lineCharToOffset(String content, int line, int col) {
        int pos = 0, curLine = 0;
        while (pos < content.length() && curLine < line) {
            if (content.charAt(pos++) == '\n') curLine++;
        }
        return Math.min(pos + col, content.length());
    }

    // -----------------------------------------------------------------------
    // JSON helpers
    // -----------------------------------------------------------------------

    private static String jsonStr(JsonObject obj, String key) {
        JsonElement el = obj.get(key);
        return (el != null && !el.isJsonNull()) ? el.getAsString() : null;
    }

    private static int jsonInt(JsonObject obj, String key, int def) {
        JsonElement el = obj.get(key);
        return (el != null && el.isJsonPrimitive()) ? el.getAsInt() : def;
    }

    private static Location jsonLocation(JsonElement locEl) {
        if (locEl == null || !locEl.isJsonObject()) return null;
        JsonObject locObj = locEl.getAsJsonObject();
        JsonElement uriEl = locObj.get("uri");
        if (uriEl == null) return null;
        JsonElement rangeEl = locObj.get("range");
        org.eclipse.lsp4j.Range range = parseRange(
                rangeEl != null && rangeEl.isJsonObject() ? rangeEl.getAsJsonObject() : null);
        return new Location(uriEl.getAsString(), range);
    }

    private static String mapStr(java.util.Map<?,?> m, String key) {
        Object v = m.get(key);
        return v instanceof String s ? s : null;
    }

    private static int mapInt(java.util.Map<?,?> m, String key, int def) {
        Object v = m.get(key);
        return v instanceof Number n ? n.intValue() : def;
    }

    private static org.eclipse.lsp4j.Range parseRangeMap(java.util.Map<?,?> rangeMap) {
        if (rangeMap == null) return zeroRange();
        Object startRaw = rangeMap.get("start");
        Object endRaw   = rangeMap.get("end");
        return new org.eclipse.lsp4j.Range(
                parsePosMap(startRaw instanceof java.util.Map<?,?> m ? m : null),
                parsePosMap(endRaw   instanceof java.util.Map<?,?> m ? m : null));
    }

    private static org.eclipse.lsp4j.Position parsePosMap(java.util.Map<?,?> posMap) {
        if (posMap == null) return new org.eclipse.lsp4j.Position(0, 0);
        return new org.eclipse.lsp4j.Position(mapInt(posMap, "line", 0),
                mapInt(posMap, "character", 0));
    }

    private static org.eclipse.lsp4j.Range parseRange(JsonObject rangeObj) {
        if (rangeObj == null) return zeroRange();
        JsonElement startEl = rangeObj.get("start");
        JsonElement endEl   = rangeObj.get("end");
        return new org.eclipse.lsp4j.Range(
                parsePosition(startEl != null && startEl.isJsonObject()
                        ? startEl.getAsJsonObject() : null),
                parsePosition(endEl   != null && endEl.isJsonObject()
                        ? endEl.getAsJsonObject()   : null));
    }

    private static org.eclipse.lsp4j.Position parsePosition(JsonObject posObj) {
        if (posObj == null) return new org.eclipse.lsp4j.Position(0, 0);
        JsonElement lineEl = posObj.get("line");
        JsonElement chEl   = posObj.get("character");
        return new org.eclipse.lsp4j.Position(
                lineEl != null ? lineEl.getAsInt() : 0,
                chEl   != null ? chEl.getAsInt()   : 0);
    }

    private static org.eclipse.lsp4j.Range zeroRange() {
        return new org.eclipse.lsp4j.Range(
                new org.eclipse.lsp4j.Position(0, 0),
                new org.eclipse.lsp4j.Position(0, 0));
    }

    // -----------------------------------------------------------------------
    // Editor / project helpers
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
}
