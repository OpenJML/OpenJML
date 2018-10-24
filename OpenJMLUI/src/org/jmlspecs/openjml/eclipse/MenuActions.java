/*
 * This file is part of the OpenJML plug-in project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.BufferedInputStream;

// FIXME - should these be combined with Commands.

import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.InputStream;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;
import org.jmlspecs.openjml.Strings;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Names;

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
    protected void initInfo(ExecutionEvent event) throws ExecutionException {
        if (Options.uiverboseness) {
            Log.log(getClass().getSimpleName() + " action initiated"); //$NON-NLS-1$
        }
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
     */
    @Override
    public Object execute(ExecutionEvent event) {
        try {
            initInfo(event);
            action();
        } catch (Exception e) {
            report(e);
        }
        return null;
    }
    
    public abstract void action();
    
    protected void report(Exception e) {
        utils.topLevelException(shell,this.getClass().getSimpleName(),e);
    }

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
		public void action() {
	        utils.changeJmlNatureSelection(true,selection,window,shell);
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
        public void action() {
			utils.changeJmlNatureSelection(false,selection,window,shell);
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
        public void action() {
    		// For now at least, only IResources are accepted for selection
    		utils.checkSelection(selection,window,shell);
    	}
    }
    
    
    public static class JMLInfer extends MenuActions {
    	
	@Override
	public void action() {
	    try {
		if (Options.uiverboseness) {
		    Log.log("INFER action initiated"); 
		}
		utils.inferSelection(selection, window, shell);
	    } catch (Exception e) {
		utils.topLevelException(shell, "MenuActions.JMLInfer", e); 
	    }
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
        public void action() {
    		utils.checkESCSelection(selection,window,shell);
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
        public void action() {
    		utils.racSelection(selection,window,shell);
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
        public void action() {
    		utils.racMarked(selection,window,shell);
    	}
    }

    /**
	 * This action enables selected resources for RAC compilation.
	 * @author David Cok
	 */
	static public class EnableForRAC extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
        public void action() {
			utils.racMark(true,selection,window,shell);
		}
	}

	/**
	 * This action disables selected resources for RAC compilation.
	 * @author David Cok
	 */
	static public class DisableForRAC extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
        public void action() {
			utils.racMark(false,selection,window,shell);
		}
	}

	/**
	 * This action opens a dialog enabling choosing the files for RAC.
	 * @author David Cok
	 */
	static public class ChooseForRAC extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
        public void action() {
	        utils.racChoose(selection,window,shell);
	    }
	}

	/**
	 * This action deletes RAC-compiled class files.
	 * @author David Cok
	 */
	static public class ClearForRAC extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
        public void action() {
	        utils.racClear(selection,window,shell);
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
        public void action() {
    		utils.deleteMarkersInSelection(selection,window,shell);
    	}
    }

    /**
	 * This action adds selected folders to the specs path.
	 */
	static public class AddToSpecsPath extends MenuActions {
	    // This is done in the UI thread. 
		@Override
        public void action() {
			utils.addSelectionToSpecsPath(selection,window,shell);
		}
	}

	/**
	 * This action removes selected folders from the specs path.
	 */
	static public class RemoveFromSpecsPath extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
        public void action() {
			utils.removeSelectionFromSpecsPath(selection,window,shell);
		}
	}

	/**
	 * This action puts up a dialog that allows manipulation of the specs path.
	 */
	static public class EditPaths extends MenuActions {
	    // This is done in the UI thread. 
	    @Override
        public void action() {
			utils.manipulateSpecsPath(selection,window,shell);
		}
	}

	/**
	 * This action puts up a dialog that shows the class, source, specs paths.
	 * @author David Cok
	 */ 
	static public class ShowPaths extends MenuActions {
	    // This is done in the UI thread. 
		@Override
        public void action() {
			utils.showPaths(selection,window,shell);
		}
	}

	/**
     * This action opens an editor containing the specifications file
     * for the selected Java classes.
     */
    static public class SpecsEditor extends MenuActions {
        // This is done in the UI thread.
        @Override
        public void action() {
    		utils.openSpecEditorForSelection(selection,window,shell);
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
        public void action() {
			utils.showSpecsForSelection(selection,window,shell);
		}
	}

	/**
     * This action pops up a dialog showing the proof result for the selected
     * Java element.
     */
    static public class ProofInformation extends MenuActions {
        @Override
        public void action() {
    		utils.showProofInfoForSelection(selection,window,shell,false);
    	}
    }

	/**
     * This action pops up a dialog showing the proof result for the selected
     * Java element.
     */
    static public class DetailedProofInformation extends MenuActions {
        @Override
        public void action() {
    		utils.showProofInfoForSelection(selection,window,shell,true);
    	}
    }

    /**
     * This action pops up a dialog showing the value of an expression in the
     * current counterexample.
     */
    static public class ShowCounterexampleValue extends MenuActions {
        // This is not done in the UI thread. // FIXME - check all statements about UI thread 
        @Override
        public void action() {
    		utils.showCEValueForTextSelection(selection,window,shell);
    	}
    }

    /**
     * This action pops up a dialog showing the value of an expression in the
     * current counterexample.
     */
    static public class ShowProofView extends MenuActions {
        // This is done in the UI thread. // FIXME - check all statements about UI thread 
        @Override
        public void action() {
            utils.showCEValueForTextSelection(selection,window,shell);
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
        public void action() {
    		utils.showMessageInUI(shell, "OpenJML - Not Yet Implemented", //$NON-NLS-1$
        				"jmldoc is not yet implemented"); //$NON-NLS-1$
            if (false) utils.jmldocSelection(selection,window,shell);
    	}
    }

	static public class CreateJmlTemplate extends MenuActions {
	    // This is all done in the UI thread with no progress monitor
	    @Override
        public void action() {
	    		utils.showMessageInUI(shell, "OpenJML", "This operation is not yet implemented");
	            ITextSelection selected = utils.getSelectedText(selection);
	            String text = selected.getText();
	            if (text.length() == 0) return ;
				IEditorPart p = window.getActivePage().getActiveEditor();
				IEditorInput e = p == null ? null : p.getEditorInput();
				IFile o = e == null ? null : (IFile) e.getAdapter(IFile.class);
				IJavaProject jp = o == null ? null : JavaCore.create(o)
						.getJavaProject();
				
				Context context = new Context();
				ClassSymbol csym = ClassReader.instance(context).loadClass(Names.instance(context).fromString(text));

				String name = text;
				int k = name.lastIndexOf('.');
				String packName = name.substring(0,k);
				String cname = name.substring(k+1);
				String dir = "/Users/davidcok/projects/OpenJML/Specs/specs";
				String filepath = dir + "/" + name.replace('.', '/') + ".jml";
				StringBuilder sb = new StringBuilder();
				sb.append("package " + packName + ";" + Strings.eol + Strings.eol);
				sb.append(Flags.toString(csym.flags()) + " class " + csym.getSimpleName()) ;
				if (!csym.getSuperclass().toString().equals("java.lang.Object")) {
					sb.append("extends ").append(csym.getSuperclass().toString());
				}
				boolean first = true;
				for (Type type: csym.getInterfaces()) {
					if (first) {
						sb.append("implements ").append(type.toString());
					} else {
						sb.append(", ").append(type.toString());
					}
				}
				
				sb.append(" {").append(Strings.eol);
				
				String indent = "    ";
				for (Symbol element: csym.getEnclosedElements()) {
					
					if (element instanceof VarSymbol) {
						VarSymbol vsym = (VarSymbol)element;
						sb.append(indent).append(Flags.toString(vsym.flags()))
								.append(" ")
								.append(vsym.type.toString())
								.append(" ")
								.append(vsym.name.toString())
								.append(";")
								.append(Strings.eol);
						
					} else if (element instanceof MethodSymbol) {
						MethodSymbol msym = (MethodSymbol)element;
						sb.append(indent)
								.append(Flags.toString(msym.flags()))
								.append(" ")
								.append(msym.getReturnType().toString())
								.append(" ")
								.append(msym.name.toString())
								.append("(")
								// Need parameters
								.append(");")
								.append(Strings.eol);
						
					} else if (element instanceof ClassSymbol) {
						// Needs to be recursive, with indentation
					}
					
				}
				sb.append(Strings.eol);
				sb.append("}" + Strings.eol);
				
				try {
				FileWriter fw = new FileWriter(filepath);
				fw.write(sb.toString());
				fw.close();
				} catch (java.io.IOException ee) {
				    throw new RuntimeException(ee);
				}
		}
	}
}
