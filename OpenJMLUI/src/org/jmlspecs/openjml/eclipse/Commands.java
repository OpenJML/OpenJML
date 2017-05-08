/*
 * This file is part of the OpenJML plug-in project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.File;
import java.io.FileWriter;
import java.util.Arrays;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IResourceRuleFactory;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.Main.Cmd;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.util.List;

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
				if (Options.uiverboseness) {
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
				if (Options.uiverboseness) {
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
	
	static public class ExportProofResults extends Commands {
	    @Override
		public Object execute(ExecutionEvent event) {
			try (FileWriter fw = new FileWriter(new File(System.getProperty("user.home") + "/resultsOutput"))) {
				if (Options.uiverboseness) {
					Log.log(this.getClass().getSimpleName() + " command initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
		    	OpenJMLView.exportProofResults(fw);
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
				if (Options.uiverboseness) {
					Log.log(this.getClass().getSimpleName() + " command initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	    		if (!utils.checkForDirtyEditors()) return null;
	    		final OpenJMLView view = utils.findView();
	    		TreeItem ti = view.selected;
	    		OpenJMLView.Info info = (OpenJMLView.Info)ti.getData();
	    		utils.findView().clearSelectedProofResults();
	    		if (info == null) return null;
	    		final String key = info.key;
	    		final IJavaElement je = info.javaElement;
	    		if (je == null) return null; // FIXME - this can happen if a default constuctor is selected - but we should still run on the file
	    		final IJavaProject jp = je.getJavaProject();
	    		final String filepath = je.getResource().getLocation().toOSString();
	    		final OpenJMLInterface iface = utils.getInterface(utils.findView().currentProject);
				utils.showView(); // Must be called from a UI thread
	    		Job j = new Job("Rerunning compilation unit " + je.getResource().getName()) {
	    			public IStatus run(IProgressMonitor monitor) {
	    				monitor.beginTask("Static checking of " + jp.getElementName(), 1);
	    				boolean c = false;
	    				try {
	    					java.util.List<String> args = iface.getOptions(iface.jproject,Cmd.ESC);
	    					args.add("-esc");
	    					args.add(filepath);
	    					iface.api.execute(null,args.toArray(new String[args.size()]));
	    					utils.setTraceView(key,jp);
	    				} catch (Exception e) {
	    					// FIXME - this will block, preventing progress on the rest of the projects
	    					Log.errorlog("Exception during Static Checking - " + je.getElementName(), e);
	    					utils.showExceptionInUI(null, "Exception during Static Checking - " + jp.getElementName(), e);
	    					c = true;
	    				}
	    				return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
	    			}
	    		};
//	            IResourceRuleFactory ruleFactory = 
//	                    ResourcesPlugin.getWorkspace().getRuleFactory();
	    		j.setRule(jp.getProject());
	    		j.setUser(true); // true since the job has been initiated by an end-user
	    		j.schedule();
	    			// FIXME - update trace and highlighting also?
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
	    		utils.showMessageInUI(shell, "OpenJML", "This operation is not yet implemented");
	            //utils.changeJmlNatureSelection(true,selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,this.getClass().getSimpleName(),e);
			}
			return null;
		}
	}

}
