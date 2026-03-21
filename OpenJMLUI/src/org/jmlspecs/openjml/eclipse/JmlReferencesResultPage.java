/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.search.ui.text.AbstractTextSearchResult;
import org.eclipse.search.ui.text.AbstractTextSearchViewPage;
import org.eclipse.search.ui.text.Match;
import org.eclipse.ui.model.WorkbenchLabelProvider;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * Search-view page for {@link JmlReferencesSearchQuery.JmlReferencesSearchResult}.
 *
 * <p>Uses only Eclipse's public search API ({@link AbstractTextSearchViewPage})
 * so it works regardless of whether the files are open in the JDT editor or
 * the Generic Editor.  Elements are {@link org.eclipse.core.resources.IFile}
 * objects; double-clicking navigates to the first match in that file.
 */
public class JmlReferencesResultPage extends AbstractTextSearchViewPage {

    public JmlReferencesResultPage() {
        super(FLAG_LAYOUT_FLAT);
    }

    @Override
    protected void configureTableViewer(TableViewer viewer) {
        viewer.setUseHashlookup(true);
        viewer.setContentProvider(new ResultContentProvider());
        viewer.setLabelProvider(new WorkbenchLabelProvider());
    }

    @Override
    protected void configureTreeViewer(TreeViewer viewer) {
        // table-only mode; not used
    }

    @Override
    protected void elementsChanged(Object[] objects) {
        StructuredViewer viewer = getViewer();
        if (viewer != null) viewer.refresh();
    }

    @Override
    protected void clear() {
        StructuredViewer viewer = getViewer();
        if (viewer != null) viewer.refresh();
    }

    @Override
    protected void showMatch(Match match, int currentOffset, int currentLength,
                             ITextEditor editor) {
        if (editor != null)
            editor.selectAndReveal(currentOffset, currentLength);
    }

    private static class ResultContentProvider implements IStructuredContentProvider {
        private static final Object[] EMPTY = new Object[0];

        @Override
        public Object[] getElements(Object input) {
            if (input instanceof AbstractTextSearchResult result)
                return result.getElements();
            return EMPTY;
        }
    }
}
