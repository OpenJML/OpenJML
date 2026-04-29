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
 * Search-view page for {@link JmlFindAllDeclarationsHandler.DeclarationSearchResult}.
 *
 * <p>Supports both flat (table) and tree modes.  In tree mode files are shown
 * as parent nodes; their {@link JmlFindAllDeclarationsHandler.DeclarationMatch}
 * children show the symbol name and kind so that double-clicking navigates
 * directly to the declaration.
 */
public class JmlDeclarationsResultPage extends AbstractTextSearchViewPage {

    public JmlDeclarationsResultPage() {
        super(FLAG_LAYOUT_FLAT | FLAG_LAYOUT_TREE);
    }

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

    @Override
    protected void handleOpen(OpenEvent event) {
        var sel = event.getSelection();
        if (sel instanceof org.eclipse.jface.viewers.IStructuredSelection ss) {
            Object first = ss.getFirstElement();
            if (first instanceof JmlFindAllDeclarationsHandler.DeclarationMatch dm
                    && dm.getElement() instanceof IFile file) {
                try {
                    IEditorPart part = IDE.openEditor(getSite().getPage(), file, true);
                    if (part instanceof ITextEditor te)
                        te.selectAndReveal(dm.getOffset(), dm.getLength());
                } catch (PartInitException e) {
                    // ignore
                }
                return;
            }
        }
        super.handleOpen(event);
    }

    @Override
    protected void showMatch(Match match, int currentOffset, int currentLength,
                             boolean activate) throws PartInitException {
        if (match.getElement() instanceof IFile file) {
            var page = org.eclipse.ui.PlatformUI.getWorkbench()
                    .getActiveWorkbenchWindow().getActivePage();
            openAndSelect(page, file, currentOffset, currentLength, activate);
        }
    }

    // -----------------------------------------------------------------------
    // Content providers
    // -----------------------------------------------------------------------

    private static class FlatContentProvider implements IStructuredContentProvider {
        private static final Object[] EMPTY = new Object[0];

        @Override
        public Object[] getElements(Object input) {
            if (input instanceof AbstractTextSearchResult r)
                return r.getElements();
            return EMPTY;
        }
    }

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

    private class ResultLabelProvider extends LabelProvider {
        private final ILabelProvider fileLabels = new WorkbenchLabelProvider();

        @Override
        public String getText(Object element) {
            if (element instanceof IFile file) {
                int n = getDisplayedMatchCount(file);
                return file.getName() + " — " + n
                        + (n == 1 ? " declaration" : " declarations");
            }
            if (element instanceof JmlFindAllDeclarationsHandler.DeclarationMatch dm) {
                String label = dm.symbolName;
                if (!dm.kindLabel.isEmpty()) label += "  [" + dm.kindLabel + "]";
                if (!dm.containerName.isEmpty()) label += " \u2014 " + dm.containerName;
                return label;
            }
            return element.toString();
        }

        @Override
        public Image getImage(Object element) {
            if (element instanceof IFile) return fileLabels.getImage(element);
            return null;
        }

        @Override
        public void dispose() {
            fileLabels.dispose();
            super.dispose();
        }
    }
}
