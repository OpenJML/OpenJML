/*
 * This file is part of the OpenJML plug-in project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * This class holds the implementations of utility classes registered against
 * menu items in the menubar and toolbar by plugin.xml
 */
public class InsertActions extends AbstractHandler {

    /** Caches the value of the window, when informed of it. */
    protected IWorkbenchWindow window;

    /** Caches the value of the shell in which the window exists. */
    protected Shell shell = null;

    /** The current selection. */
    protected ISelection selection;

    /** Cached value of the utility object */
    protected Utils utils = Activator.utils();

    /** Populates the class fields with data about the event, for use in the
     * derived classes.
     */
    protected void getInfo(ExecutionEvent event) throws ExecutionException {
        window = HandlerUtil.getActiveWorkbenchWindowChecked(event);
        shell = window.getShell();
        selection = window.getSelectionService().getSelection();
    }

    /**
     * We can use this method to dispose of any system
     * resources we previously allocated.
     * @see org.eclipse.core.commands.IHandler#dispose()
     */
    @Override
    public void dispose() {
        super.dispose();
    }

    public final static int offset = "insert ".length();

    /** Called by the system in response to a menu selection (or other command).
     * This should be overridden for individual menu items.
     */
    @Override
    public Object execute(ExecutionEvent event) {
        try {
            String commandName = event.getCommand().getName();
            String keyword = commandName.substring(offset);
            if (true || Options.uiverboseness) {
                Log.log("Insert " + keyword + " action initiated"); //$NON-NLS-1$
            }
            getInfo(event);

            ITextSelection selectedText = utils.getSelectedText(selection);
            if (selectedText == null) {
                Utils.showMessage(shell, "JML", "No cursor location found");
                return null;
            }
            int pos = selectedText.getOffset();
            IEditorPart activeEditor = PlatformUI.getWorkbench()
                                    .getActiveWorkbenchWindow()
                                    .getActivePage()
                                    .getActiveEditor();
            StyledText styledText = (StyledText)activeEditor.getAdapter(Control.class);
            styledText.replaceTextRange(pos,selectedText.getLength(),keyword);
            if (keyword.contains(";")) {
                int k = keyword.lastIndexOf(' ');
                styledText.setSelection(pos + k + 1,pos + keyword.length() - 1);

            } else {
                styledText.setCaretOffset(pos + keyword.length());
            }

        } catch (Exception e) {
            utils.topLevelException(shell,"InsertActions ",e); //$NON-NLS-1$
        }
        return null;
    }

    //	static public class Requires extends InsertActions {
    //		public String keyword() { return "requires "; }
    //	}
    //
    //	static public class Result extends InsertActions {
    //		public String keyword() { return "\\result"; }
    //	}


}
