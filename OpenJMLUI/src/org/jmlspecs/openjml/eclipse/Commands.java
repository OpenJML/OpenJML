/*
 * This file is part of the OpenJML plug-in project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;

import com.sun.tools.javac.code.Symbol;

/**
 * This class holds the implementations of utility classes registered against
 * menu items in the menubar and toolbar by plugin.xml
 */
abstract public class Commands extends AbstractHandler {

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

    /** Called by the system in response to a menu selection (or other command).
     * This should be overridden for individual menu items.
     */
    @Override
    abstract public Object execute(ExecutionEvent event);

    /**
	 * This action enables the JML nature on the selected projects,
	 * so that checking happens as part of compilation.
	 * 
	 * @author David Cok
	 *
	 */
	static public class ClearAllProofResults extends Commands {
	    // This is all done in the UI thread with no progress monitor
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (true || Options.uiverboseness) {
					Log.log(this.getClass().getSimpleName() + " command initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.findView().clearProofResults();
	        } catch (Exception e) {
	            utils.topLevelException(shell,this.getClass().getSimpleName(),e);
			}
			return null;
		}
	}

	static public class ClearSelectedProofResults extends Commands {
	    // This is all done in the UI thread with no progress monitor
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (true || Options.uiverboseness) {
					Log.log(this.getClass().getSimpleName() + " command initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.findView().clearSelectedProofResults();
	        } catch (Exception e) {
	            utils.topLevelException(shell,this.getClass().getSimpleName(),e);
			}
			return null;
		}
	}

	static public class RerunStaticCheck extends Commands {
	    // This is all done in the UI thread with no progress monitor
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (true || Options.uiverboseness) {
					Log.log(this.getClass().getSimpleName() + " command initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	    		Symbol sym = utils.findView().currentSymbol;
	    		OpenJMLInterface iface = utils.getInterface(utils.findView().currentProject);
	    		if (sym instanceof Symbol.MethodSymbol) {
	    			iface.api.doESC((Symbol.MethodSymbol)sym);
	    			utils.showView();
	    			// FIXME - update trace and highlighting also?
	    		} else if (sym instanceof Symbol.ClassSymbol) {
	    			iface.api.doESC((Symbol.ClassSymbol)sym);
	    			utils.showView();
	    		}
	            //utils.changeJmlNatureSelection(true,selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,this.getClass().getSimpleName(),e);
			}
			return null;
		}
	}

	static public class ShowResultsForProblem extends Commands {
	    // This is all done in the UI thread with no progress monitor
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (true || Options.uiverboseness) {
					Log.log(this.getClass().getSimpleName() + " command initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            //utils.changeJmlNatureSelection(true,selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,this.getClass().getSimpleName(),e);
			}
			return null;
		}
	}

}
