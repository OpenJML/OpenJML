/*
 * Copyright (c) 2006 David R. Cok
 * @author David R. Cok
 * Created Nov 17, 2006
 */
package org.jmlspecs.openjml.eclipse;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

/**
 * This class holds the implementations of the utils in response to
 * menu items in the menubar and toolbar
 */
abstract public class MenuActions implements IWorkbenchWindowActionDelegate {

    // IWorkbenchWindowActionDelegate is the interface for actions that
    // are contributed as menubar or toolbar items

    /** Caches the value of the window, when informed of it. */
    protected IWorkbenchWindow window;

    /** Caches the value of the shell in which the window exists. */
    protected Shell shell = null;

    /** The current selection. */
    protected ISelection selection;

    /** Cached value of the utility object */
    protected Utils utils = Activator.getDefault().utils;
    
    /* (non-Javadoc)
     * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
     */
    //JAVA16 @Override
    public final void selectionChanged(final IAction action, final ISelection selection) {
        this.selection = selection;
    }

    /**
     * We can use this method to dispose of any system
     * resources we previously allocated.
     * @see IWorkbenchWindowActionDelegate#dispose
     */
    //JAVA16 @Override
    public void dispose() {
    }

    /**
     * We will cache window object in order to
     * be able to provide a parent shell for the message dialog.
     * @param window The parent window
     * @see IWorkbenchWindowActionDelegate#init
     */
    //JAVA16 @Override
    public void init(IWorkbenchWindow window) {
        this.window = window;
        this.shell = window.getShell();
    }

    /** Called by the system in response to a menu selection (or other command).
     * This should be overridden for individual menu items.
     */
    //JAVA16 @Override
    abstract public void run(final IAction action);

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
        public final void run(final IAction action) {
            // For now at least, only IResources are accepted for selection
            try {
                utils.checkSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.CheckJML",e);
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
        public final void run(final IAction action) {
            try {
                Activator.getDefault().utils.checkESCSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.CheckESC",e);
            }
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
        public final void run(final IAction action) {
            try {
                Activator.getDefault().utils.racSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.RAC",e);
            }
        }
    }

    /**
     * This class implements the action that clears
     * JML markers.  It is performed entirely in the UI thread, with no
     * progress reporting.  Its ought to be fast.
     * 
     * @author David R. Cok
     */
    public static class DeleteMarkers extends MenuActions {
        @Override
        public final void run(final IAction action) {
            try {
                utils.deleteMarkersInSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.DeleteMarkers",e);
            }
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
        // This is all done in the UI thread with no progress
        @Override
        public final void run(final IAction action) {
            try {
                utils.changeJmlNatureSelection(true,selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.EnableJML",e);
            }
        }
    }

    /**
     * This action disables the JML nature on the selected projects.
     * 
     * @author David Cok
     *
     */
    static public class DisableJML extends MenuActions {
        // This is all done in the UI thread with no progress
        @Override
        public final void run(final IAction action) {
            try {
                Activator.getDefault().utils.changeJmlNatureSelection(false,selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.DisableJML",e);
            }
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
        public final void run(final IAction action) {
            try {
                utils.showSpecsForSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.CheckJML",e);
            }
        }
    }

    /**
     * This action pops up a dialog showing the prroof result for the selected
     * Java element.
     * 
     * @author David Cok
     *
     */
    static public class ShowCounterexample extends MenuActions {
        // This is mostly done in the UI thread.  Gathering and formatting
        // the specs for display should be fast, unless the specs actually
        // need to be computed; that computation is done in a computation
        // thread.  However, the display of specs has to wait for that to
        // complete in any case.
        @Override
        public final void run(final IAction action) {
            try {
                utils.showProofInfoForSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.ShowCounterexample",e);
            }
        }
    }

    /**
     * This action adds selected folders to the specs path.
     * @author David Cok
     */
    static public class AddToSpecsPath extends MenuActions {
        // This is done in the UI thread. 
        @Override
        public final void run(final IAction action) {
            try {
                utils.addSelectionToSpecsPath(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.AddToSpecsPath",e);
            }
        }
    }

    /**
     * This action removes selected folders from the specs path.
     * @author David Cok
     */
    static public class RemoveFromSpecsPath extends MenuActions {
        // This is done in the UI thread. 
        @Override
        public final void run(final IAction action) {
            try {
                utils.removeSelectionFromSpecsPath(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.RemoveFromSpecsPath",e);
            }
        }
    }

    /**
     * This action puts up a dialog that allows manipulation of the specs path.
     * @author David Cok
     */
    static public class SpecsPath extends MenuActions {
        // This is done in the UI thread. 
        @Override
        public final void run(final IAction action) {
            try {
                utils.manipulateSpecsPath(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.SpecsPath",e);
            }
        }
    }

    /**
     * This action puts up a dialog that allows manipulation of the class path.
     * @author David Cok
     */
    static public class ClassPath extends MenuActions {
        // This is done in the UI thread. 
        @Override
        public final void run(final IAction action) {
            try {
                utils.manipulateClassPath(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.ClassPath",e);
            }
        }
    }

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
        //        ProjectInfo pi = ProjectInfo.getProjectInfo(((IJavaElement)o).getJavaProject());
        //        if (pi == null) {
        //          pi = new ProjectInfo(Activator.options,JMLBuilder.preq);
        //          pi.setJavaProject(((IJavaElement)o).getJavaProject());
        //        }
        //        final ProjectInfo ppi = pi;
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
        //              t = Types.getSuperClass(t,pi);
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
        //              st = Types.getSuperClass(st,pi);
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
        //          List<IFolder> locations = pi.getLocations(packagename);
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
        // except for the actual creating of the specs path folders,
        // since for some reason that can take a long time
        @Override
        public final void run(final IAction action) {
            try {
                utils.jmldocSelection(selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,"MenuActions.JmlDoc",e);
            }
        }
    }


        /**
         * This action edits the specspath and sets up the appropriate
         * structure for the new specs path.  No selection is needed or
         * paid attention to (for now - until the specspath is made 
         * dependent on the project).
         * 
         * @author David Cok
         *
         */
        static public class EditSpecsPath extends MenuActions {  // TODO
            // This is all done in the UI thread with no progress,
            // except for the actual creating of the specs path folders,
            // since for some reason that can take a long time
            @Override
            public final void run(final IAction action) {
                try {
                    IStatus result = editSpecsPath(shell);
                    Log.log((result == Status.OK_STATUS ? "Completed" : "Cancelled") +
                    " Edit specs path operation ");
                } catch (Exception e) {
                    utils.topLevelException(shell,"MenuActions.CheckJML",e);
                }
            }


        /** Internal helper routine to do the work of editing the specs path
         * @param shell the shell to own the windows
         * @return a Status value, e.g. OK_STATUS or CANCEL_STATUS
         */
        private IStatus editSpecsPath(Shell shell) {
            // At the moment, the specsProject is independent of project, so we don't
            // require any project selection to edit the path
            //      final ProjectInfo pi = new ProjectInfo(Activator.options,JMLBuilder.preq);
            //      specsProjectText = pi.options.specsProjectName;
            //      EditPath d = new EditPath(shell);
            //      boolean ok = d.open() == Window.OK;
            //      if (!ok) return Status.CANCEL_STATUS;
            //      pi.options.specsProjectName = specsProjectText;
            //      final Shell sh = shell;
            //      Job j = new Job("Creating specs project") {
            //        public IStatus run(IProgressMonitor monitor) {
            //          // FIXME - should we provide a way to cancel this?  it might leave things in a bad state?
            //          pi.specsproject = pi.createEmptyJavaProject(specsProjectText,true,true);  // FIXME - errors?
            //          String errors = pi.createSpecspathFolders(listItems);
            //          if (errors != null) showMessageInUI(sh,"JML Plugin",errors);
            //          return Status.OK_STATUS;
            //        }
            //      };
            //      j.setUser(true);
            //      j.schedule();
            //      IStatus res = j.getResult();
            //      if (res == Status.CANCEL_STATUS) return res;
            return Status.OK_STATUS;
        }
    }

    /** Just used to communicate between editSpecspath() and EditPath.
     * Note that the EditPath dialog gets disposed and not completely
     * usable after the open() call returns.
     */
    String[] listItems = null;
    //String[] listItems = new String[] { "C:/Data/Users/L593102/ESC/runtime-JML3UI/LocalSpecs/src","C:/Data/Users/L593102/ESC/runtime-JML3UI/Jml3Sandbox/src", "C:/home/JML3/JML3Core/specs", ""};

    /** Keeps the previous list of items, so that the user can revert if desired."
     */
    String[] previousListItems = null;

    /** Just used to communicate between editSpecspath() and EditPath.
     * Note that the EditPath dialog gets disposed and not completely
     * usable after the open() call returns.
     */
    private String specsProjectText = null;

    /** This class holds functionality to allow editing the specs path in the UI */
    public class EditPath extends Dialog {

        /** The wdiget that hold sthe list of path items */
        org.eclipse.swt.widgets.List listcontrol;

        /** The widget that holds the name of the specs project. */
        Text specsProjectField;

        /** The text widget for the directory browser */
        Widgets.DirTextField dirTextField;

        /** The constructor, obviously. 
         * @param shell the parent shell used for new windows
         */
        public EditPath(Shell shell) { super(shell); }

        // FIXME - the sizes of the text field, the file browser field and the list
        // are not appearing as they should
        protected Control createDialogArea(Composite parent) {
            Log.log("Creating dialog area");
            Composite composite = (Composite)super.createDialogArea(parent);
            Composite vv = new Widgets.VComposite(composite);
            Composite hh = new Widgets.HComposite(vv,2);
            new Label(hh,SWT.CENTER).setText("Specifications project name");
            specsProjectField = new Text(hh,SWT.SINGLE);
            // FIXME - The spaces are just to make the field bigger - find a better way
            specsProjectField.setText(specsProjectText + "             ");
            // FIXME - the following does not work either
            specsProjectField.setSize(specsProjectField.getSize().x*5,specsProjectField.getLineHeight());
            dirTextField = new Widgets.DirTextField(vv,"Directory or jar file to add","","A widget that browses for directories to be added to the specs path",50);
            final Widgets.DirTextField f = dirTextField;
            Composite w = new Widgets.HComposite(vv,2);
            listcontrol = new org.eclipse.swt.widgets.List(w, SWT.V_SCROLL|SWT.BORDER|SWT.SINGLE);
            final org.eclipse.swt.widgets.List list = listcontrol;
            listcontrol.addSelectionListener(new SelectionListener() {
                public void widgetSelected(SelectionEvent e) { 
                    int i = list.getSelectionIndex();
                    Log.log("Statemask " + e.stateMask + " " + i + " " + list.getItem(i));
                    if (i<0) f.setText(list.getItem(i));  // FIXME - this is not working
                    list.select(i);
                    list.setFocus();
                };
                public void widgetDefaultSelected(SelectionEvent e) {
                    Log.log("Default selected " + e.stateMask);
                }
            });
            Composite v = new Widgets.VComposite(w);
            Button b = new Button(v,SWT.PUSH|SWT.CENTER);
            b.addSelectionListener(new SelectionListener() {
                public void widgetSelected(SelectionEvent e) { 
                    int i = list.getSelectionIndex();
                    //Log.log("ADD " + i + " " + f.value() + " " + list.getTopIndex());
                    if (i == -1) i = list.getItemCount()-1;
                    list.add(f.value(),i);
                    list.select(i);
                    list.setFocus();
                }
                public void widgetDefaultSelected(SelectionEvent e) {}
            });
            b.setText("Add");
            b = new Button(v,SWT.PUSH|SWT.CENTER);
            b.addSelectionListener(new SelectionListener() {
                public void widgetSelected(SelectionEvent e) { 
                    int i = list.getSelectionIndex();
                    //Log.log("ADD " + i + " " + f.value() + " " + list.getTopIndex());
                    if (i == -1) i = list.getItemCount()-1;
                    //            try {
                    String s = "<internal specs>"; //JmlDriver.internalspecs();
                    list.add(s,i);
                    list.select(i);
                    list.setFocus();
                    //            } catch (IOException ee) {
                    //              showMessage(shell,"JML UI Plugin Exception","Failed to find the internal specs library - see the error log");
                    //              Log.errorlog("Failed to find the internal specs library",ee);
                    //            }
                }
                public void widgetDefaultSelected(SelectionEvent e) {}
            });
            b.setText("Add Internal Specs");
            b = new Button(v,SWT.PUSH|SWT.CENTER);
            b.addSelectionListener(new SelectionListener() {
                public void widgetSelected(SelectionEvent e) { 
                    int i = list.getSelectionIndex();
                    //Log.log("REPLACE " + i + " " + e.text + " " + f.value());
                    if ( i >= 0 && i < list.getItemCount()-1) {
                        list.remove(i);
                        list.add(f.value(),i);
                        list.select(i);
                        list.setFocus();
                    }
                }
                public void widgetDefaultSelected(SelectionEvent e) {}
            });
            b.setText("Replace");
            b = new Button(v,SWT.PUSH|SWT.CENTER);
            b.addSelectionListener(new SelectionListener() {
                public void widgetSelected(SelectionEvent e) { 
                    int i = list.getSelectionIndex();
                    //Log.log("REMOVE " + i);
                    // May not remove the last blank line
                    if (i >= 0 && i < list.getItemCount()-1) {
                        list.remove(i);
                        list.setFocus();
                    }
                }
                public void widgetDefaultSelected(SelectionEvent e) {}
            });
            b.setText("Remove");
            b = new Button(v,SWT.PUSH|SWT.CENTER);
            b.addSelectionListener(new SelectionListener() {
                public void widgetSelected(SelectionEvent e) { 
                    int i = list.getSelectionIndex();
                    //Log.log("UP " + i);
                    // The test on getTopIndex is to prevent the last blank line
                    // from being moved
                    if (i > 0 && i < list.getItemCount()-1) {
                        String s = list.getItem(i);
                        list.remove(i);
                        list.add(s,i-1);
                        list.select(i-1);
                        list.setFocus();
                    }
                }
                public void widgetDefaultSelected(SelectionEvent e) {}
            });
            b.setText("Up");
            b = new Button(v,SWT.PUSH|SWT.CENTER);
            b.addSelectionListener(new SelectionListener() {
                public void widgetSelected(SelectionEvent e) { 
                    int i = list.getSelectionIndex();
                    //Log.log("DOWN " + i + " " + list.getTopIndex());
                    if (i < list.getItemCount()-2) {
                        String s = list.getItem(i);
                        list.remove(i);
                        list.add(s,i+1);
                        list.select(i+1);
                        list.setFocus();
                    }
                }
                public void widgetDefaultSelected(SelectionEvent e) {}
            });
            b.setText("Down");

            b = new Button(v,SWT.PUSH|SWT.CENTER);
            b.addSelectionListener(new SelectionListener() {
                public void widgetSelected(SelectionEvent e) { 
                    //Log.log("REVERT ");
                    if (previousListItems != null) {
                        list.setItems(previousListItems);
                    }
                    list.setFocus();
                }
                public void widgetDefaultSelected(SelectionEvent e) {}
            });
            b.setText("Revert");

            // Now find the existing list of specs path items
            IProject p = ResourcesPlugin.getWorkspace().getRoot().getProject(specsProjectText);
            List<String> listloc = null;
            if (p!= null && p.exists()) {
                IJavaProject jp = JavaCore.create(p);
                if (jp != null && jp.exists()) {
                    IFolder ff = p.getFolder(Env.specsContainerName);
                    int i = 0;
                    listloc = new LinkedList<String>();
                    if (ff != null && ff.exists()) {
                        while (true) {
                            String s = Env.specsFolderRoot + (++i);
                            IFolder fs = ff.getFolder(s);
                            if (fs == null || !fs.exists()) break;
                            String loc = fs.getRawLocation().toOSString();
                            //Log.log("FOLDER " + loc);
                            listloc.add(loc);
                        }
                        listloc.add("");
                    }
                }
            }
            if (listloc == null) {
                //          try {
                String specs = "<<internal specs>>"; //JmlDriver.internalspecs();
                listItems = new String[]{specs,""};
                //          } catch (IOException e) {
                //            Log.errorlog("Failed to find the internal specs library",e);
                //            showMessage(shell,"JML Plugin Exception","Failed to find the internal specs library (see error log): " + e);
                //            // No change in this case
                //            return composite;
                //          }
            } else {
                listItems = listloc.toArray(new String[listloc.size()]); // ALWAYS HAVE A LAST BLANK ITEM
            }
            list.setItems(listItems);
            list.setSize(list.getSize().y, list.getItemHeight()*10);
            Log.log((listloc.size()-1) + " specs path items detected in the existing specs project named " + specsProjectText);
            return composite;
        }

        protected void configureShell(Shell newShell) {
            super.configureShell(newShell);
            newShell.setText("Specs path editor");
        }

        protected void okPressed() {
            // FIXME should we do some checking and not exit if there are
            // problems (e.g. entries that are duplicates or do not exist)
            previousListItems = listItems;
            listItems = listcontrol.getItems();
            specsProjectText = specsProjectField.getText().trim();
            super.okPressed();
        }
    }
}
