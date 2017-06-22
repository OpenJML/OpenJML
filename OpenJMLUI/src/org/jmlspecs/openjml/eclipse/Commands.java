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
import org.jmlspecs.openjml.Main;
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
	    		if (view == null || view.selectedList.isEmpty()) return null;
	    		
				utils.showView(); // Must be called from a UI thread
				final OpenJMLInterface iface = utils.getInterface(utils.findView().currentProject);
				IJavaProject jp = iface.jproject;
				final java.util.List<IJavaElement> args = new java.util.LinkedList<>();

				for (TreeItem ti : view.selectedList) {
					OpenJMLView.Info info = (OpenJMLView.Info)ti.getData();
					if (info == null) continue;
					String key = info.key;
					IJavaElement je = info.javaElement;
					if (je == null) continue; // FIXME - this can happen if a default constructor is selected - but we should still run on the file
					String filepath = je.getResource().getLocation().toOSString();
					args.add(je);
				}
				String title = "Rerunning selected items from project " + jp.getResource().getName();
				Job j = new Job(title) {
					public IStatus run(IProgressMonitor monitor) {
						monitor.beginTask(title, 1);
						monitor.subTask("Detailed progress will be shown only if the verbosity preference is at least 'progress'");
						boolean c = false;
						try {
							iface.executeESCCommand(Main.Cmd.ESC, args, monitor);
							//iface.api.execute(null,args.toArray(new String[args.size()]));
						} catch (Exception e) {
							// FIXME - this will block, preventing progress on the rest of the projects
							Log.errorlog("Exception during Static Checking - " + jp.getElementName(), e);
							utils.showExceptionInUI(null, "Exception during Static Checking - " + jp.getElementName(), e);
							c = true;
						}
						return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
					}
				};
	    		j.setRule(jp.getProject()); // FIXME - this locks teh whole project - is that what we want?
	    		j.setUser(true); // true since the job has been initiated by an end-user
	    		j.schedule();
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
