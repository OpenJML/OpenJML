/* This file is part of the OpenJML plugin project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

// FIXME - needs to be changed to Eclipse 4.2

/** This class and its inner classes implement the various utilities
 * that are defined when a right-mouse click is performed on menu items
 * in the Package Navigator and other similar Views.  The class names
 * must be in synch with the information in the plug-in definition.
 */
abstract public class PopupActions implements IObjectActionDelegate {

    /** A cached value of the most recent selection */
    protected ISelection selection;

    /** A cached value of the shell */
    protected Shell shell;
    
    /** A cached value of the utilities object */
    protected Utils utils = Activator.utils();

    /** The method that is called when the menu item is activated. */
    @Override
    abstract public void run(IAction action);

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction,
     *      org.eclipse.jface.viewers.ISelection)
     */
    @Override
    public void selectionChanged(IAction action, ISelection selection) {
        this.selection = selection;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.ui.IObjectActionDelegate#setActivePart(org.eclipse.jface.action.IAction,
     *      org.eclipse.ui.IWorkbenchPart)
     */
    @Override
    public void setActivePart(IAction action, IWorkbenchPart targetPart) {
        this.shell = targetPart.getSite().getShell();
    }


    /** This class implements the 'EnableNature' action, which adds the
     * JML Natures to a Java Project.
     */
    public static class EnableJMLNature extends PopupActions {
        // This is all done in the UI thread with no progress
        @Override
        public final void run(final IAction action) {
            try {
    			if (Options.uiverboseness) {
    				Log.log("Enable JML context action initiated"); //$NON-NLS-1$
    			}
                utils.changeJmlNatureSelection(true,selection,null,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"PopupActions.EnableJML",e); //$NON-NLS-1$
            }
        }
    }

    /** This class implements the 'DeleteNature' action, which removes
     * the JML Nature from a Java Project.  This menu item
     * is only enabled for Java Projects.
     */
    public static class DisableJMLNature extends PopupActions {
        // This is all done in the UI thread with no progress
        @Override
        public final void run(final IAction action) {
            try {
    			if (Options.uiverboseness) {
    				Log.log("Disable JML context action initiated"); //$NON-NLS-1$
    			}
                utils.changeJmlNatureSelection(false,selection,null,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"PopupActions.DisableJML",e); //$NON-NLS-1$
            }
        }
    }

    /** This class implements the action of type-checking JML for
	 *  a resource (recursively, for containers).
	 */
	public static class CheckJML extends PopupActions {
	    @Override
	    public void run(IAction action) {
	        try {
				if (Options.uiverboseness) {
					Log.log("Type-check JML context action initiated"); //$NON-NLS-1$
				}
	            utils.checkSelection(selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.CheckJML",e); //$NON-NLS-1$
	        }
	    }
	}

	/** This class implements the action of static checking for
	 *  a resource (recursively, for containers).
	 */
	public static class CheckESC extends PopupActions {
	    @Override
	    public void run(IAction action) {
	        try {
				if (Options.uiverboseness) {
					Log.log("ESC context action initiated"); //$NON-NLS-1$
				}
	            utils.checkESCSelection(selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.CheckESC",e); //$NON-NLS-1$
	        }
	    }
	}

	/** This class implements the action of compiling runtime checks for
	 *  a resource (recursively, for containers).
	 */
	public static class RAC extends PopupActions {
	    @Override
	    public void run(IAction action) {
	        try{
				if (Options.uiverboseness) {
					Log.log("RAC context action initiated"); //$NON-NLS-1$
				}
	            utils.racSelection(selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.RAC",e); //$NON-NLS-1$
	        }
	    }
	}

	/**
	 * This action enables selected resources for RAC compilation.
	 * @author David Cok
	 */
	static public class EnableForRAC extends PopupActions {
	    // This is done in the UI thread. 
	    @Override
	    public final void run(final IAction action) {
	        try {
				if (Options.uiverboseness) {
					Log.log("Mark For RAC context action initiated"); //$NON-NLS-1$
				}
	            utils.racMark(true,selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.EnableForRac",e); //$NON-NLS-1$
	        }
	    }
	}

	/**
	 * This action disables selected resources from RAC compilation.
	 * @author David Cok
	 */
	static public class DisableForRAC extends PopupActions {
	    // This is done in the UI thread. 
	    @Override
	    public final void run(final IAction action) {
	        try {
				if (Options.uiverboseness) {
					Log.log("Unmark For RAC context action initiated"); //$NON-NLS-1$
				}
	            utils.racMark(false,selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.DisableForRac",e); //$NON-NLS-1$
	        }
	    }
	}

	/**
	 * This action opens a dialog enabling choosing the files for RAC.
	 * @author David Cok
	 */
	static public class ChooseForRAC extends PopupActions {
	    // This is done in the UI thread. 
	    @Override
	    public final void run(final IAction action) {
	        try {
				if (Options.uiverboseness) {
					Log.log("Choose For RAC action initiated"); //$NON-NLS-1$
				}
	            utils.racChoose(selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.ChooseForRac",e); //$NON-NLS-1$
	        }
	    }
	}

	/**
	 * This action deletes RAC-compiled class files.
	 * @author David Cok
	 */
	static public class ClearForRAC extends PopupActions {
	    // This is done in the UI thread. 
	    @Override
	    public final void run(final IAction action) {
	        try {
				if (Options.uiverboseness) {
					Log.log("Clear RAC Marks context action initiated"); //$NON-NLS-1$
				}
	            utils.racClear(selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.ClearForRac",e); //$NON-NLS-1$
	        }
	    }
	}

	/** This class implements the action of deleting all the JML markers
	 * in everything selected (recursively, for containers).  It is completed
	 * in the UI thread, without a progress monitor.
	 */
	public static class DeleteJMLMarkers extends PopupActions {
	    @Override
	    public final void run(final IAction action) {
	        try {
				if (Options.uiverboseness) {
					Log.log("Delete Markers context action initiated"); //$NON-NLS-1$
				}
	            utils.deleteMarkersInSelection(selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.DeleteJMLMarkers",e); //$NON-NLS-1$
	        }
	    }
	}

	/**
	 * This action adds selected folders to the specs path.
	 * @author David Cok
	 */
	static public class AddToSpecsPath extends PopupActions {
	    // This is done in the UI thread. 
	    @Override
	    public final void run(final IAction action) {
	        try {
				if (Options.uiverboseness) {
					Log.log("Add To Specs Path context action initiated"); //$NON-NLS-1$
				}
	            utils.addSelectionToSpecsPath(selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.AddToSpecsPath",e); //$NON-NLS-1$
	        }
	    }
	}

	/**
	 * This action removes selected folders from the specs path.
	 * @author David Cok
	 */
	static public class RemoveFromSpecsPath extends PopupActions {
	    // This is done in the UI thread. 
	    @Override
	    public final void run(final IAction action) {
	        try {
				if (Options.uiverboseness) {
					Log.log("Remove From Specs Path context action initiated"); //$NON-NLS-1$
				}
	            utils.removeSelectionFromSpecsPath(selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.RemoveFromSpecsPath",e); //$NON-NLS-1$
	        }
	    }
	}

	/**
     * This action puts up a dialog that allows manipulation of the specs path.
     */
    static public class EditPaths extends PopupActions {
        // This is done in the UI thread. 
        @Override
        public final void run(final IAction action) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("Edit Paths action initiated"); //$NON-NLS-1$
    			}
                utils.manipulateSpecsPath(selection,null,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.SpecsPath",e); //$NON-NLS-1$
    		}
    	}
    }

	/**
     * This action puts up a dialog that shows the class, source, specs paths.
     * @author David Cok
     */ 
    static public class ShowPaths extends PopupActions {
        // This is done in the UI thread. 
    	@Override
        public final void run(final IAction action) {
    		try {
    			if (Options.uiverboseness) {
    				Log.log("Show Paths action initiated"); //$NON-NLS-1$
    			}
                utils.showPaths(selection,null,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.ShowPaths",e); //$NON-NLS-1$
    		}
    	}
    }


    /**
     * This action opens an editor containing the specifications file
     * for the selected Java classes.
     * 
     * @author David Cok
     *
     */
    static public class SpecsEditor extends PopupActions {
        // This is done in the UI thread.
        @Override
        public final void run(final IAction action) {
            try {
    			if (Options.uiverboseness) {
    				Log.log("Specs Editor context action initiated"); //$NON-NLS-1$
    			}
                utils.openSpecEditorForSelection(selection,null,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.SpecsEditor",e); //$NON-NLS-1$
            }
        }
    }
    
    
    public static class InferSpecs extends PopupActions {
	@Override
	public void run(IAction action) {
	    try {
		if (Options.uiverboseness) {
		    Log.log("Infer context action initiated"); //$NON-NLS-1$
		}
		utils.inferSelection(selection, null, shell);
	    } catch (Exception e) {
		utils.topLevelException(shell, "PopupActions.InferJML", e); //$NON-NLS-1$
	    }
	}
    }

    /** This class implements the action of popping up a dialog to
	 * show specifications of a Java element.
	 */
	public static class ShowSpecs extends PopupActions {
	    @Override
	    public void run(IAction action) {
	        try{
				if (Options.uiverboseness) {
					Log.log("Show Specifications context action initiated"); //$NON-NLS-1$
				}
	            utils.showSpecsForSelection(selection,null,shell);
	        } catch (Exception e) {
	            utils.topLevelException(shell,"PopupActions.ShowSpecs",e); //$NON-NLS-1$
	        }
	    }
	}

	/** This class implements the action of popping up a dialog to
     * show the counterexample for a Java method.
     */
    public static class ProofInformation extends PopupActions {
        @Override
        public void run(IAction action) {
            try {
    			if (Options.uiverboseness) {
    				Log.log("Show Proof Information context action initiated"); //$NON-NLS-1$
    			}
                utils.showProofInfoForSelection(selection,null,shell,false);
            } catch (Exception e) {
                utils.topLevelException(shell,"PopupActions.ShowCounterexample",e); //$NON-NLS-1$
            }
        }
    }

	/** This class implements the action of popping up a dialog to
     * show the counterexample for a Java method.
     */
    public static class ShowCounterexampleValue extends PopupActions {
        @Override
        public void run(IAction action) {
            try {
    			if (Options.uiverboseness) {
    				Log.log("Show Counterexample action initiated"); //$NON-NLS-1$
    			}
                utils.showCEValueForTextSelection(selection,null,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"PopupActions.ShowCounterexampleValue",e); //$NON-NLS-1$
            }
        }
    }


    /**
     * This action generates jmldoc documentation for selected projects (and
     * for projects whose elements are selected).
     * @author David Cok
     */
    static public class JmlDoc extends PopupActions {
        @Override
        public final void run(final IAction action) {
            try {
    			if (Options.uiverboseness) {
    				Log.log("JML doc context action initiated"); //$NON-NLS-1$
    			}
        		utils.showMessageInUI(shell, "OpenJML - Not Yet Implemented", //$NON-NLS-1$
        				"jmldoc is not yet implemented"); //$NON-NLS-1$
                if (false) utils.jmldocSelection(selection,null,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"PopupActions.JmlDoc",e); //$NON-NLS-1$
            }
        }
    }

}
