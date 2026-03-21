/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.net.URI;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.lsp4e.LanguageServers;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.ReferenceParams;
import org.eclipse.search.ui.ISearchQuery;
import org.eclipse.search.ui.ISearchResult;
import org.eclipse.search.ui.text.AbstractTextSearchResult;
import org.eclipse.search.ui.text.IEditorMatchAdapter;
import org.eclipse.search.ui.text.IFileMatchAdapter;
import org.eclipse.search.ui.text.Match;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

/**
 * LSP-backed {@link ISearchQuery} that calls {@code textDocument/references}
 * on the OpenJML LSP server and populates Eclipse's Search view.
 */
public class JmlReferencesSearchQuery implements ISearchQuery {

    private static final int LSP_TIMEOUT_SEC = 30;
    private static final String PLUGIN_ID = "org.openjml.OpenJMLUI";

    private final IDocument                document;
    private final String                   symbolName;
    private final ReferenceParams          params;
    private final Shell                    shell;
    private final JmlReferencesSearchResult searchResult;

    public JmlReferencesSearchQuery(IDocument document, String symbolName,
                                    ReferenceParams params, Shell shell) {
        this.document     = document;
        this.symbolName   = symbolName;
        this.params       = params;
        this.shell        = shell;
        this.searchResult = new JmlReferencesSearchResult(this);
    }

    // -----------------------------------------------------------------------
    // ISearchQuery
    // -----------------------------------------------------------------------

    @Override
    public IStatus run(IProgressMonitor monitor) {
        searchResult.removeAll();

        List<? extends Location> locations;
        try {
            locations = LanguageServers.forDocument(document)
                    .computeFirst(server ->
                            server.getTextDocumentService().references(params))
                    .get(LSP_TIMEOUT_SEC, TimeUnit.SECONDS)
                    .orElse(List.of());
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return Status.CANCEL_STATUS;
        } catch (Exception e) {
            notifyError("textDocument/references failed: " + e.getMessage());
            return new Status(IStatus.ERROR, PLUGIN_ID,
                    "textDocument/references failed: " + e.getMessage(), e);
        }

        if (locations.isEmpty()) {
            Display.getDefault().asyncExec(() ->
                    MessageDialog.openInformation(shell, "Find References",
                            "No references found for '" + symbolName + "'."));
            return Status.OK_STATUS;
        }

        Map<IFile, String> contentCache = new HashMap<>();
        for (Location loc : locations) {
            if (monitor.isCanceled()) return Status.CANCEL_STATUS;
            IFile file = uriToFile(loc.getUri());
            if (file == null) continue;
            String content = contentCache.computeIfAbsent(file,
                    JmlReferencesSearchQuery::readFileContent);
            int start = lineCharToOffset(content,
                    loc.getRange().getStart().getLine(),
                    loc.getRange().getStart().getCharacter());
            int end   = lineCharToOffset(content,
                    loc.getRange().getEnd().getLine(),
                    loc.getRange().getEnd().getCharacter());
            searchResult.addMatch(new Match(file, start, Math.max(0, end - start)));
        }
        return Status.OK_STATUS;
    }

    @Override public ISearchResult  getSearchResult()    { return searchResult; }
    @Override public String         getLabel()           { return "OpenJML: Find References to '" + symbolName + "'"; }
    @Override public boolean        canRerun()           { return true; }
    @Override public boolean        canRunInBackground() { return true; }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    private void notifyError(String msg) {
        Display.getDefault().asyncExec(() ->
                MessageDialog.openError(shell, "Find References", msg));
    }

    private static IFile uriToFile(String uriStr) {
        try {
            IFile[] files = ResourcesPlugin.getWorkspace().getRoot()
                    .findFilesForLocationURI(new URI(uriStr));
            return files.length > 0 ? files[0] : null;
        } catch (Exception e) {
            return null;
        }
    }

    private static String readFileContent(IFile file) {
        try (java.io.InputStream is = file.getContents()) {
            return new String(is.readAllBytes(), java.nio.charset.StandardCharsets.UTF_8);
        } catch (Exception e) {
            return "";
        }
    }

    private static int lineCharToOffset(String content, int line, int col) {
        int offset = 0, currentLine = 0;
        while (offset < content.length() && currentLine < line) {
            if (content.charAt(offset++) == '\n') currentLine++;
        }
        return Math.min(offset + col, content.length());
    }

    // -----------------------------------------------------------------------
    // Inner result class
    // -----------------------------------------------------------------------

    static class JmlReferencesSearchResult extends AbstractTextSearchResult {

        private final JmlReferencesSearchQuery query;

        JmlReferencesSearchResult(JmlReferencesSearchQuery query) {
            this.query = query;
        }

        @Override
        public String getLabel() {
            int n = getMatchCount();
            return n + (n == 1 ? " reference" : " references")
                    + " to '" + query.symbolName + "'";
        }

        @Override public ImageDescriptor getImageDescriptor() { return null; }
        @Override public ISearchQuery    getQuery()           { return query; }

        @Override
        public IFileMatchAdapter getFileMatchAdapter() {
            return new IFileMatchAdapter() {
                @Override
                public Match[] computeContainedMatches(
                        AbstractTextSearchResult result, IFile file) {
                    return result.getMatches(file);
                }
                @Override
                public IFile getFile(Object element) {
                    return element instanceof IFile f ? f : null;
                }
            };
        }

        @Override
        public IEditorMatchAdapter getEditorMatchAdapter() {
            return null;
        }
    }
}
