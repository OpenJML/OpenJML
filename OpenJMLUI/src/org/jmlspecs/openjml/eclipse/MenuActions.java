/*
 * Copyright (c) 2006-2011 David R. Cok
 * @author David R. Cok
 * Created Nov 17, 2006
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
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
    protected Utils utils = Activator.getDefault().utils;
    
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
    }

    /** Called by the system in response to a menu selection (or other command).
     * This should be overridden for individual menu items.
     */
    @Override
    abstract public Object execute(ExecutionEvent event);

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
        		getInfo(event);
    			utils.checkSelection(selection,window,shell);
    		} catch (Exception e) {
    			utils.topLevelException(shell,"MenuActions.CheckJML",e);
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
    		// For now at least, only IResources are accepted for selection
    		try {
        		getInfo(event);
                utils.checkESCSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.CheckESC",e);
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
        		getInfo(event);
                utils.racSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.RAC",e);
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
        		getInfo(event);
        		utils.deleteMarkersInSelection(selection,window,shell);
    		} catch (Exception e) {
    			utils.topLevelException(shell,"MenuActions.DeleteJMLMarkers",e);
    		}
    		return null;
    	}
    }

    /**
     * This action enables the JML nature on the selected projects,
     * so that checking happens as part of compilation.
     * 
     * @author David Cok
     *
     */
    static public class EnableJML extends MenuActions {
        // This is all done in the UI thread with no progress monitor
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
        		getInfo(event);
                utils.changeJmlNatureSelection(true,selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.EnableJML",e);
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
    static public class DisableJML extends MenuActions {
        // This is all done in the UI thread with no progress monitor
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
        		getInfo(event);
                utils.changeJmlNatureSelection(false,selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.DisableJML",e);
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
        		getInfo(event);
                utils.showSpecsForSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.ShowSpecs",e);
    		}
    		return null;
    	}
    }

    /**
     * This action opens an editor containing the specifications file
     * for the selected Java classes.
     * 
     * @author David Cok
     *
     */ // FIXME - no longer used I believe since now we edit specs in the Preferences page
    static public class SpecsEditor extends MenuActions {
        // This is done in the UI thread.
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
        		getInfo(event);
                utils.openSpecEditorForSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.SpecsEditor",e);
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
        		getInfo(event);
                utils.showProofInfoForSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.ShowProofInformation",e);
    		}
    		return null;
    	}
    }

    /**
     * This action pops up a dialog showing the value of an expression in the
     * current counterexample.
     */
    static public class ShowCounterexampleValue extends MenuActions {
        // This is not done in the UI thread.  
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
        		getInfo(event);
                utils.showCEValueForTextSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.ShowCounterexampleValue",e);
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
        		getInfo(event);
                utils.addSelectionToSpecsPath(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.AddToSpecsPath",e);
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
        		getInfo(event);
                utils.removeSelectionFromSpecsPath(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.RemoveFromSpecsPath",e);
    		}
    		return null;
    	}
    }

    /**
     * This action puts up a dialog that allows manipulation of the specs path.
     */  // FIXME - is this still used?
    static public class SpecsPath extends MenuActions {
        // This is done in the UI thread. 
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
        		getInfo(event);
                utils.manipulateSpecsPath(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.SpecsPath",e);
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
        		getInfo(event);
                utils.showPaths(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.ShowPaths",e);
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
        		getInfo(event);
                utils.markForRac(true,selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.EnableForRac",e);
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
        		getInfo(event);
                utils.markForRac(false,selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.DisableForRac",e);
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
            	getInfo(event);
                utils.clearForRac(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.ClearForRac",e);
            }
            return null;
        }
    }

    // FIXME - implement showSpecs
    /** A static helper method that can be called for PopupActions
     * as well - it puts up an informational dialog with specification
     * information about the object o.  This may spawn a computational
     * task.
     * @param shell the shell responsible for the dialog window
     * @param o the object whose specs are to be shown
     * @return a Status value indicating whether a cancel occurred
     */
    public static IStatus showSpecs(Shell shell, /*@ non_null */ Object o) {
        //      try {
        //        ProjectInfo jproject = ProjectInfo.getProjectInfo(((IJavaElement)o).getJavaProject());
        //        if (jproject == null) {
        //          jproject = new ProjectInfo(Activator.options,JMLBuilder.preq);
        //          jproject.setJavaProject(((IJavaElement)o).getJavaProject());
        //        }
        //        final ProjectInfo ppi = jproject;
        //        final Shell sh = shell;
        //        String title,content;
        //        if (o instanceof IType) {
        //          final IType tt = (IType)o;
        //          IType t = tt;
        //          title = "Specifications of type " + t.getFullyQualifiedName();
        //          JmlSpecifications.TypeDeclSpecs s = JmlSpecifications.findTypeSpecs(t);
        //          StringBuilder ss = new StringBuilder();
        //          if (s == null) {
        //            // spawning a computational thread here
        //            Job j = new Job("JML - getting type specs") {
        //              public IStatus run(IProgressMonitor monitor) {
        //                try {
        //                  (new OpenJMLInterface(ppi)).getSpecs(tt,TypeInfo.State.JML_SIGNATURE_ONLY,monitor);
        //                } catch (Exception e) {
        //                  String msg = "An exception occurred while computing the specs for type " +
        //                  tt.getFullyQualifiedName() + ": " + e;
        //                  showMessageInUI(sh,"JML Plugin Exception",msg);
        //                  Log.errorlog(msg,e);
        //                }
        //                if (monitor.isCanceled()) return Status.CANCEL_STATUS;
        //                return Status.OK_STATUS;
        //              }
        //            };
        //            j.setUser(true);
        //            j.schedule();
        //            j.join();
        //            IStatus result = j.getResult();
        //            if (result != Status.OK_STATUS) return result;
        //            s = JmlSpecifications.findTypeSpecs(t);
        //          } 
        //          if (s == null) {
        //            ss.append("No specs cached or generated");
        //          } else {
        //            for (JmlTypeSpecification j: s.typeSpecs) {
        //              ss.append(JmlASTCodeWriter.generateSnippets(j));
        //            }
        //            while (true) {
        //              t = Types.getSuperClass(t,jproject);
        //              if (t == null) break;
        //              s = JmlSpecifications.findTypeSpecs(t);
        //              ss.append("\nSpecifications of super type " + t.getFullyQualifiedName() + "\n");
        //              for (JmlTypeSpecification j: s.typeSpecs) {
        //                ss.append(JmlASTCodeWriter.generateSnippets(j));
        //              }
        //            }
        //            // FIXME - need interface specs
        //          }
        //          content = ss.toString();
        //        } else if (o instanceof ICompilationUnit) {
        //          final ICompilationUnit t = (ICompilationUnit)o;
        //          JmlSpecifications.CompUnitSpecs s = JmlSpecifications.findCUSpecs(t);
        //          StringBuilder ss = new StringBuilder();
        //          if (s == null) {
        //            // spawning a computational thread here
        //            Job j = new Job("JML - getting compilation unit specs") {
        //              public IStatus run(IProgressMonitor monitor) {
        //                try {
        //                  OpenJMLInterface jmlc = new OpenJMLInterface(ppi);
        //                  jmlc.getSpecs(t,TypeInfo.State.JML_SIGNATURE_ONLY,monitor);
        //                } catch (Exception e) {
        //                  String msg = "An exception occurred while computing the specs for compilation unit " +
        //                  t.getElementName() + ": " + e;
        //                  showMessageInUI(sh,"JML Plugin Exception",msg);
        //                  Log.errorlog(msg,e);
        //                }
        //                if (monitor.isCanceled()) return Status.CANCEL_STATUS;
        //                return Status.OK_STATUS;
        //              }
        //            };
        //            j.setUser(true);
        //            j.schedule();
        //            j.join();
        //            IStatus res = j.getResult();
        //            if (res == Status.CANCEL_STATUS) return res;
        //            s = JmlSpecifications.findCUSpecs(t);
        //          } 
        //          if (s == null) {
        //            ss.append("No specs cached or generated");
        //          } else {
        //            for (JmlModelImportDeclaration j: s.modelImports) {
        //              ss.append(JmlASTCodeWriter.generateSnippets(j));
        //            }
        //            ss.append(s.modelTypes.size() + " model types\n");
        //            if (s.specssequence == null || s.specssequence.size() == 0) {
        //              ss.append("No specification refinement sequence found\n" +
        //                      "THIS IS A PROBLEM - check that your specs path is correct.\n" +
        //                      "You may need to include your .java files on your specs path");
        //            } else {
        //              ss.append("The specification refinement sequence:\n");
        //              for (IFile f: s.specssequence) {
        //                ss.append(f.getLocation().toOSString() + "\n");
        //              }
        //            }
        //          }
        //          content = ss.toString();
        //          title = "Specifications of compilation unit " + t.getResource().getLocation().toOSString();
        //        } else if (o instanceof IMethod) {
        //          final IMethod m = (IMethod)o;
        //          title = "Specifications of method " + m.getElementName();
        //          Log.log("Showing " + title);
        //          JmlSpecifications.MethodDeclSpecs s = JmlSpecifications.findMethodSpecs(m);
        //          StringBuilder ss = new StringBuilder();
        //          if (s == null) {
        //            // spawning a computational thread here
        //            Job j = new Job("JML - getting method specs") {
        //              public IStatus run(IProgressMonitor monitor) {
        //                try {
        //                  (new OpenJMLInterface(ppi)).getSpecs(m.getDeclaringType(),TypeInfo.State.JML_SIGNATURE_ONLY,monitor);
        //                } catch (Exception e) {
        //                  String msg = "An exception occurred while computing the specs for method " +
        //                      m.getElementName() + ": " + e;
        //                  showMessageInUI(sh,"JML Plugin Exception",msg);
        //                  Log.errorlog(msg,e);
        //                }
        //                if (monitor.isCanceled()) return Status.CANCEL_STATUS;
        //                return Status.OK_STATUS;
        //              }
        //            };
        //            j.setUser(true);
        //            j.schedule();
        //            j.join();
        //            IStatus res = j.getResult();
        //            if (res == Status.CANCEL_STATUS) return res;
        //            s = JmlSpecifications.findMethodSpecs(m);
        //          } 
        //          boolean showParsed = true;
        //          if (s == null) {
        //            ss.append("No specs cached");
        //          } else {
        //            if (!showParsed) {
        //              //ss.append("Raw specs:\n");
        //              for (JmlMethodSpecification ms: s.raw) {
        //                ss.append(JmlASTCodeWriter.generateSnippets(ms));
        //              }
        //            }
        //            if (showParsed) {
        //              if (s.parsed != null) {
        //                //ss.append("\nParsed specs:\n");
        //                for (JmlMethodSpecificationCase ms: s.parsed) {
        //                  ss.append(JmlASTCodeWriter.generateSnippets(ms));
        //                }
        //              }
        //            }
        //            IMethod mfirst = m;
        //            IType st = m.getDeclaringType();
        //            while (true) {
        //              st = Types.getSuperClass(st,jproject);
        //              if (st == null) break;
        //              IMethod[] meths = st.findMethods(mfirst);
        //              if (meths == null || meths.length == 0) continue;
        //              if (meths.length > 1) {
        //                Log.log("Ambiguous method " + mfirst + " in super type " + st.getElementName());
        //                break;
        //              }
        //              s = JmlSpecifications.findMethodSpecs(meths[0]);
        //              ss.append("\nSpecifications from super type " + st.getFullyQualifiedName() + "\n");
        //              if (!showParsed) {
        //                for (JmlMethodSpecification ms: s.raw) {
        //                  ss.append(JmlASTCodeWriter.generateSnippets(ms));
        //                }
        //              }
        //              if (showParsed && s.parsed != null) {
        //                //ss.append("\nParsed specs:\n");
        //                for (JmlMethodSpecificationCase ms: s.parsed) {
        //                  ss.append(JmlASTCodeWriter.generateSnippets(ms));
        //                }
        //              }
        //            }
        //          }
        //          // FIXME - get method specs from super interfaces as well
        //          content = ss.toString();
        //        } else if (o instanceof IField) {
        //          IField t = (IField)o;
        //          title = "Specifications of field " + t.getElementName();
        //          content = "              ????\n  ?????";
        //        } else if (o instanceof IPackageFragment) {
        //          String packagename = ((IPackageFragment)o).getElementName();
        //          List<IFolder> locations = jproject.getLocations(packagename);
        //          title = "Locations for package " + packagename;
        //          content = "Files for package " + packagename + " are located at\n";
        //          for (IFolder f: locations) {
        //            content += "    " + f.getLocation().toOSString() + "\n";
        //          }
        //          // FIXME - should we show the specs path for completeness
        //          // We could show that for projects as well
        //        } else if (o instanceof IJavaElement) {
        //          IJavaElement t = (IJavaElement)o;
        //          title = "Specifications of Java element " + t.getElementName();
        //          content = "Sorry, presentation of the specfications of a " + t.getClass() + " is not implemented";
        //        } else if (o instanceof IResource) {
        //          IMethod t = (IMethod)o;
        //          title = "Specifications of method " + t.getElementName();
        //          content = "              ????\n  ?????";
        ////        } else if (o == null) {
        ////          title = "JML Specifications";
        ////          content = "Cannot present specifications of a null object";
        //        } else {
        //          title = "JML Specifications";
        //          content = "I did not expect to be called with an object of type " + o.getClass();
        //        }
        //        showSpecsDialog(shell,title,content);
        //      } catch (Exception e) {
        //        String msg = "Exception while showing specs "
        //          + (o != null ? "for a " + o.getClass() : "") + e;
        //        Log.errorlog(msg,e);
        //        if (shell != null) {
        //          showMessage(shell,"Show Specs exception ",
        //                  e.toString());
        //        }           
        //      }
        return Status.OK_STATUS;
    }

    /** A String array used to define the buttons in a show specs dialog */
    final private static String[] okbutton = { "OK" };

    /** Pops up a dialog showing the given content.
     * @param shell the shell that should own the dialog window
     * @param title the title of the dialog
     * @param content the text content of the dialog
     */
    // FIXME - I broke out this function in the hope that we can eventually
    // provide a better display - allow the use of bold font or labels, perhaps
    // be non-modal, perhaps include the JML logo
    public static void showSpecsDialog(Shell shell, String title, String content) {
        //MessageDialog.openInformation(shell,title,content);
        MessageDialog m = new MessageDialog(shell,title,null,content,MessageDialog.NONE,
                okbutton,0);
        m.open();
        //(new ShowSpecsDialog(shell,title,content)).open();
    }

    // The following is a starting point for an alternate display.
    // Not used at present.
    //    public static class ShowSpecsDialog extends Dialog { //PopupDialog {
    //      protected String  content;
    //      protected String title;
    //
    //      /**
    //       * Creates a new ShowSpecsDialog.
    //       */
    ////      public ShowSpecsDialog(Shell parentShell, IJavaElement input) {
    ////        super(parentShell, SWT.DEFAULT, false, // do not take focus when opened
    ////                false, // do not persist the bounds
    ////                false, // do not show a resize menu
    ////                false, // do not show a menu item for persisting bounds
    ////                "Specs for " + input.getElementName(),
    ////                null); // no info text - FIXME
    ////        this.input = input;
    ////      }
    //      public ShowSpecsDialog(Shell parentShell, String title, String content) {
    //        super(parentShell);
    //        
    //        this.title = title;
    //        this.content = content;
    //      }
    //      
    //      protected void configureShell(Shell newShell) {
    //        super.configureShell(newShell);
    //        newShell.setText(title);
    //     }
    //      
    //      public Control createDialogArea(Composite composite) {
    //        Text t = new Text(composite,SWT.READ_ONLY|SWT.READ_ONLY);
    //        t.setText(content);
    //        t.setSize(500,500);
    //        return t;
    //      }
    //    }


    /**
     * This action generates jmldoc html pages for any selected project
     * (or for projects whose elements are selected).
     * @author David Cok
     */
    static public class JmlDoc extends MenuActions {
        // This is all done in the UI thread with no progress,
        // except for the actual creating of the specs path folders, // FIXME - this comment is not correct
        // since for some reason that can take a long time
        @Override
    	public Object execute(ExecutionEvent event) {
    		try {
        		getInfo(event);
                utils.jmldocSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.JmlDoc",e);
    		}
    		return null;
    	}
    }


}
