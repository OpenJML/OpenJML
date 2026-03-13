package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jdt.ui.text.java.hover.IJavaEditorTextHover;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;

/** This class implements showing counterexample information when
 * hovering over source code identifiers and expressions.
 */
public class CounterexampleHover implements IJavaEditorTextHover {

    IEditorPart editor;
    IResource res;
    IJavaProject currentProject;

    @Override
    public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
        try {
            //Object o = ((CompilationUnitEditor)textViewer).
            if (res == null) return null;
            int pos = hoverRegion.getOffset();
            int end = pos + hoverRegion.getLength();
            String value = Activator.utils().getInterface(currentProject).getCEValue(pos, end, null, res);
            //if (value != null) Log.log("Counterexample hover: " + value);
            return value == null ? null : ("Counterexample: " + value);
        } catch (Exception e) {
            return null;
        }
    }

    @Override
    public IRegion getHoverRegion(ITextViewer textViewer, int offset) {
        Point selection= textViewer.getSelectedRange();
        if (selection.x <= offset && offset < selection.x + selection.y)
            return new Region(selection.x, selection.y);
        return new Region(offset, 0);
    }

    @Override
    public void setEditor(IEditorPart editor) {
        this.editor = editor;
        try {
            IEditorInput einput = editor.getEditorInput();
            res = (IResource)einput.getAdapter(IResource.class);

            IFileEditorInput input = (IFileEditorInput) einput;
            IProject p = input.getFile().getProject();
            currentProject = p.hasNature(JavaCore.NATURE_ID) ? JavaCore.create(p) : null;
        } catch (Exception e) {
            res = null;
            currentProject = null;
        }
    }

}
