/*
 * This file is part of the OpenJML plug-in project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * This class holds the implementations of utility classes registered against
 * menu items in the menubar and toolbar by plugin.xml
 */
abstract public class MenuActions extends AbstractHandler {

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
	static public class EnableJMLNature extends MenuActions {
	    // This is all done in the UI thread with no progress monitor
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (Options.uiverboseness) {
					Log.log("Enable JML action initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.changeJmlNatureSelection(true,selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.EnableJML",e); //$NON-NLS-1$
			}
			return null;
		}
	}

	/**
	 * This action disables the JML nature on the selected projects.
	 * 
	 * @author David Cok
	 *
	 */
	static public class DisableJMLNature extends MenuActions {
	    // This is all done in the UI thread with no progress monitor
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (Options.uiverboseness) {
					Log.log("Disable JML action initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.changeJmlNatureSelection(false,selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.DisableJML",e); //$NON-NLS-1$
			}
			return null;
		}
	}

	/**
     * This class implements the action for checking
     * JML in the selected objects (which may be working sets, folders,
     * or java files).  Applying the operation
     * to a container applies it to all its contents recursively.
     * The checks are done in a non-UI thread.
     * 
     * @author David R. Cok
     */
    public static class CheckJML extends MenuActions {
    	@Override
    	public Object execute(ExecutionEvent event) {
    		// For now at least, only IResources are accepted for selection
    		try {
    			if (Options.uiverboseness) {
    				Log.log("Type-check action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
    			utils.checkSelection(selection,window,shell);
    		} catch (Exception e) {
    			utils.topLevelException(shell,"MenuActions.CheckJML",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }
    
    
    public static class JMLInfer extends MenuActions {
    	@Override
    	public Object execute(ExecutionEvent event) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("INFER action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
                utils.inferSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.JMLInfer",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }

    
    

    /** This class implements the action for doing ESC on the selected objects -
     * which may be any folder, java file, working set or class or method.
     * Applying the operation
     * to a container applies it to all its contents recursively.
     * The processing is done in a non-UI thread.
     * @author David R. Cok
     *
     */
    public static class CheckESC extends MenuActions {
    	@Override
    	public Object execute(ExecutionEvent event) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("ESC action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
                utils.checkESCSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.CheckESC",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }

    /** This class implements the action for compiling RAC on the selected objects -
     * which may be any folder, java file, working set.  Applying the operation
     * to a container applies it to all its contents recursively.
     * The processing is done in a non-UI thread.
     * @author David R. Cok
     *
     */
    public static class RAC extends MenuActions {
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("RAC action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
                utils.racSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.RAC",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }

    /** This class implements the action for compiling RAC on the marked objects.
     * Applying the operation
     * to a container applies it to all its contents recursively.
     * The processing is done in a non-UI thread.
     * @author David R. Cok
     *
     */
    public static class RACMarked extends MenuActions {
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("RAC Marked files action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
                utils.racMarked(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.RACMarked",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }

    /**
	 * This action enables selected resources for RAC compilation.
	 * @author David Cok
	 */
	static public class EnableForRAC extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (Options.uiverboseness) {
					Log.log("Mark for RAC action initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.racMark(true,selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.EnableForRac",e); //$NON-NLS-1$
			}
			return null;
		}
	}

	/**
	 * This action disables selected resources for RAC compilation.
	 * @author David Cok
	 */
	static public class DisableForRAC extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (Options.uiverboseness) {
					Log.log("Unmark For RAC action initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.racMark(false,selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.DisableForRac",e); //$NON-NLS-1$
			}
			return null;
		}
	}

	/**
	 * This action opens a dialog enabling choosing the files for RAC.
	 * @author David Cok
	 */
	static public class ChooseForRAC extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
	    public Object execute(ExecutionEvent event) {
	        try {
				if (Options.uiverboseness) {
					Log.log("Choose For RAC action initiated"); //$NON-NLS-1$
				}
	        	getInfo(event);
	            utils.racChoose(selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.ChooseForRac",e); //$NON-NLS-1$
	        }
	        return null;
	    }
	}

	/**
	 * This action deletes RAC-compiled class files.
	 * @author David Cok
	 */
	static public class ClearForRAC extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
	    public Object execute(ExecutionEvent event) {
	        try {
				if (Options.uiverboseness) {
					Log.log("Clear RAC Marks action initiated"); //$NON-NLS-1$
				}
	        	getInfo(event);
	            utils.racClear(selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.ClearForRac",e); //$NON-NLS-1$
	        }
	        return null;
	    }
	}

	/**
     * This class implements the action that clears
     * JML markers.  It is performed entirely in the UI thread, with no
     * progress reporting.  It ought to be fast.
     * 
     * @author David R. Cok
     */
    public static class DeleteJMLMarkers extends MenuActions {
    	@Override
    	public Object execute(ExecutionEvent event) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("Delete Markers action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
        		utils.deleteMarkersInSelection(selection,window,shell);
    		} catch (Exception e) {
    			utils.topLevelException(shell,"MenuActions.DeleteJMLMarkers",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }

    /**
	 * This action adds selected folders to the specs path.
	 */
	static public class AddToSpecsPath extends MenuActions {
	    // This is done in the UI thread. 
		@Override
		public Object execute(ExecutionEvent event) {
			try {
				if (Options.uiverboseness) {
					Log.log("Add To Specs Path action initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.addSelectionToSpecsPath(selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.AddToSpecsPath",e); //$NON-NLS-1$
			}
			return null;
		}
	}

	/**
	 * This action removes selected folders from the specs path.
	 */
	static public class RemoveFromSpecsPath extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (Options.uiverboseness) {
					Log.log("Remove From Specs Path action initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.removeSelectionFromSpecsPath(selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.RemoveFromSpecsPath",e); //$NON-NLS-1$
			}
			return null;
		}
	}

	/**
	 * This action puts up a dialog that allows manipulation of the specs path.
	 */
	static public class EditPaths extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (Options.uiverboseness) {
					Log.log("Edit Paths action initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.manipulateSpecsPath(selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.SpecsPath",e); //$NON-NLS-1$
			}
			return null;
		}
	}

	/**
	 * This action puts up a dialog that shows the class, source, specs paths.
	 * @author David Cok
	 */ 
	static public class ShowPaths extends MenuActions {
	    // This is done in the UI thread. 
		@Override
		public Object execute(ExecutionEvent event) {
			try {
				if (Options.uiverboseness) {
					Log.log("Show Paths action initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.showPaths(selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.ShowPaths",e); //$NON-NLS-1$
			}
			return null;
		}
	}

	/**
     * This action opens an editor containing the specifications file
     * for the selected Java classes.
     */
    static public class SpecsEditor extends MenuActions {
        // This is done in the UI thread.
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("Open Specs Editor action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
                utils.openSpecEditorForSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.SpecsEditor",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }

    /**
	 * This action pops up a dialog showing the specs for the selected
	 * Java element.
	 * 
	 * @author David Cok
	 *
	 */
	static public class ShowSpecs extends MenuActions {
	    // This is mostly done in the UI thread.  Gathering and formatting
	    // the specs for display should be fast, unless the specs actually
	    // need to be computed; that computation is done in a computation
	    // thread.  However, the display of specs has to wait for that to
	    // complete in any case.
	    @Override
		public Object execute(ExecutionEvent event) {
			try {
				if (Options.uiverboseness) {
					Log.log("Show Specifications action initiated"); //$NON-NLS-1$
				}
	    		getInfo(event);
	            utils.showSpecsForSelection(selection,window,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"MenuActions.ShowSpecs",e); //$NON-NLS-1$
			}
			return null;
		}
	}

	/**
     * This action pops up a dialog showing the proof result for the selected
     * Java element.
     */
    static public class ProofInformation extends MenuActions {
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("Show Proof Information action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
                utils.showProofInfoForSelection(selection,window,shell,false);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.ShowProofInformation",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }

	/**
     * This action pops up a dialog showing the proof result for the selected
     * Java element.
     */
    static public class DetailedProofInformation extends MenuActions {
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("Show Proof Information action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
                utils.showProofInfoForSelection(selection,window,shell,true);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.DetailedShowProofInformation",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }

    /**
     * This action pops up a dialog showing the value of an expression in the
     * current counterexample.
     */
    static public class ShowCounterexampleValue extends MenuActions {
        // This is not done in the UI thread. // FIXME - check all statements about UI thread 
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("Show Counterexample action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
                utils.showCEValueForTextSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.ShowCounterexampleValue",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }

    /**
     * This action pops up a dialog showing the value of an expression in the
     * current counterexample.
     */
    static public class ShowProofView extends MenuActions {
        // This is done in the UI thread. // FIXME - check all statements about UI thread 
        @Override
    	public Object execute(ExecutionEvent event) {
    		utils.refreshView();
    		return null;
    	}
    }

    /**
     * This action generates jmldoc html pages for any selected project
     * (or for projects whose elements are selected).
     * @author David Cok
     */
    static public class JmlDoc extends MenuActions {
        // This is all done in the UI thread with no progress,
        // except for the actual creating of the specs path folders, // FIXME - this comment is not correct; function not yet implemented
        // since for some reason that can take a long time
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("JMLdoc action initiated"); //$NON-NLS-1$
    			}
        		getInfo(event);
        		utils.showMessageInUI(shell, "OpenJML - Not Yet Implemented", //$NON-NLS-1$
        				"jmldoc is not yet implemented"); //$NON-NLS-1$
                if (false) utils.jmldocSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.JmlDoc",e); //$NON-NLS-1$
    		}
    		return null;
    	}
    }


}
