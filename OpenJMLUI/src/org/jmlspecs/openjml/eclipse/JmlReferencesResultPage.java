/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.search.ui.text.AbstractTextSearchResult;
import org.eclipse.search.ui.text.AbstractTextSearchViewPage;
import org.eclipse.search.ui.text.Match;
import org.eclipse.swt.graphics.Image;
import org.eclipse.jface.viewers.OpenEvent;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.model.WorkbenchLabelProvider;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * Search-view page for {@link JmlReferencesSearchQuery.JmlReferencesSearchResult}.
 *
 * <p>Supports both flat (table) and tree modes.  In tree mode files are shown
 * as parent nodes; their {@link JmlReferencesSearchQuery.LocatedMatch} children
 * show the 1-indexed line number and stripped source text so that
 * double-clicking a child navigates directly to that location.
 */
public class JmlReferencesResultPage extends AbstractTextSearchViewPage {

    public JmlReferencesResultPage() {
        super(FLAG_LAYOUT_FLAT | FLAG_LAYOUT_TREE);
    }

    // -----------------------------------------------------------------------
    // Viewer configuration
    // -----------------------------------------------------------------------

    @Override
    protected void configureTableViewer(TableViewer viewer) {
        viewer.setUseHashlookup(true);
        viewer.setContentProvider(new FlatContentProvider());
        viewer.setLabelProvider(new ResultLabelProvider());
    }

    @Override
    protected void configureTreeViewer(TreeViewer viewer) {
        viewer.setUseHashlookup(true);
        viewer.setContentProvider(new TreeContentProvider());
        viewer.setLabelProvider(new ResultLabelProvider());
    }

    @Override
    protected void elementsChanged(Object[] objects) {
        StructuredViewer v = getViewer();
        if (v != null) v.refresh();
    }

    @Override
    protected void clear() {
        StructuredViewer v = getViewer();
        if (v != null) v.refresh();
    }

    /**
     * In tree mode the base-class {@code handleOpen} only toggles expand/collapse
     * and never reaches {@code showMatch}.  Override to navigate directly when a
     * {@link JmlReferencesSearchQuery.LocatedMatch} leaf is double-clicked.
     */
    @Override
    protected void handleOpen(org.eclipse.jface.viewers.OpenEvent event) {
        org.eclipse.jface.viewers.ISelection sel = event.getSelection();
        if (sel instanceof org.eclipse.jface.viewers.IStructuredSelection ss) {
            Object first = ss.getFirstElement();
            if (first instanceof JmlReferencesSearchQuery.LocatedMatch lm
                    && lm.getElement() instanceof IFile file) {
                try {
                    IEditorPart part = IDE.openEditor(getSite().getPage(), file, true);
                    if (part instanceof ITextEditor te)
                        te.selectAndReveal(lm.getOffset(), lm.getLength());
                } catch (PartInitException e) {
                    // ignore
                }
                return;
            }
        }
        // IFile nodes: let the base class handle (expand/collapse)
        super.handleOpen(event);
    }

    @Override
    protected void showMatch(Match match, int currentOffset, int currentLength,
                             boolean activate) throws org.eclipse.ui.PartInitException {
        // Called by gotoNextMatch / showCurrentMatch (table mode and keyboard nav).
        if (match.getElement() instanceof org.eclipse.core.resources.IFile file) {
            org.eclipse.ui.IWorkbenchPage page =
                org.eclipse.ui.PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
            openAndSelect(page, file, currentOffset, currentLength, activate);
        }
    }

    // -----------------------------------------------------------------------
    // Content providers
    // -----------------------------------------------------------------------

    /** Flat mode: top-level elements are IFile nodes. */
    private static class FlatContentProvider implements IStructuredContentProvider {
        private static final Object[] EMPTY = new Object[0];

        @Override
        public Object[] getElements(Object input) {
            if (input instanceof AbstractTextSearchResult r)
                return r.getElements();
            return EMPTY;
        }
    }

    /** Tree mode: IFile → LocatedMatch[]. */
    private static class TreeContentProvider implements ITreeContentProvider {
        private static final Object[] EMPTY = new Object[0];
        private AbstractTextSearchResult result;

        @Override
        public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
            result = newInput instanceof AbstractTextSearchResult r ? r : null;
        }

        @Override
        public Object[] getElements(Object input) {
            return result != null ? result.getElements() : EMPTY;
        }

        @Override
        public Object[] getChildren(Object parent) {
            if (result != null && parent instanceof IFile file)
                return result.getMatches(file);
            return EMPTY;
        }

        @Override
        public boolean hasChildren(Object element) {
            return result != null && element instanceof IFile file
                    && result.getMatchCount(file) > 0;
        }

        @Override
        public Object getParent(Object element) {
            return element instanceof Match m ? m.getElement() : null;
        }
    }

    // -----------------------------------------------------------------------
    // Label provider
    // -----------------------------------------------------------------------

    /**
     * Shows file name + match count for {@link IFile} nodes, and
     * "line N: text" for {@link JmlReferencesSearchQuery.LocatedMatch} leaves.
     */
    private class ResultLabelProvider extends LabelProvider {
        private final ILabelProvider fileLabels = new WorkbenchLabelProvider();

        @Override
        public String getText(Object element) {
            if (element instanceof IFile file) {
                int n = getDisplayedMatchCount(file);
                return file.getName() + " — " + n + (n == 1 ? " reference" : " references");
            }
            if (element instanceof JmlReferencesSearchQuery.LocatedMatch lm)
                return lm.line + ": " + lm.lineText;
            return element.toString();
        }

        @Override
        public Image getImage(Object element) {
            if (element instanceof IFile)
                return fileLabels.getImage(element);
            return null;
        }

        @Override
        public void dispose() {
            fileLabels.dispose();
            super.dispose();
        }
    }
}
