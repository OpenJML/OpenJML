/*
 * This file is part of the OpenJML plug-in project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.Arrays;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.State;
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
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.handlers.RadioState;
import org.eclipse.ui.handlers.RegistryToggleState;
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

    //** The Command that is being responded to */
    protected Command command;

    /** Cached value of the utility object */
    protected Utils utils = Activator.utils();

    /** Populates the class fields with data about the event, for use in the
     * derived classes.
     */
    protected void initInfo(ExecutionEvent event) throws ExecutionException {
        if (Options.uiverboseness) {
            Log.log(this.getClass().getSimpleName() + " command initiated"); //$NON-NLS-1$
        }
        window = HandlerUtil.getActiveWorkbenchWindowChecked(event);
        shell = window.getShell();
        selection = window.getSelectionService().getSelection();
        command = event.getCommand(); 
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

    static public class ToggleAutoOpen extends Commands {
        // This is all done in the UI thread with no progress monitor
        @Override
        public Object execute(ExecutionEvent event) {
            try {
                initInfo(event);
                boolean oldValue = HandlerUtil.toggleCommandState(command);
                //                State state = command.getState(RegistryToggleState.STATE_ID);
                //                state.setValue(!oldValue);
                utils.findView().toggleAutoOpen(!oldValue);
            } catch (Exception e) {
                utils.topLevelException(shell,this.getClass().getSimpleName(),e);
            }
            return null;
        }
    }

    static public class RadioAutoOpen extends Commands {
        // This is all done in the UI thread with no progress monitor
        @Override
        public Object execute(ExecutionEvent event) {
            try {
                initInfo(event);
                if(HandlerUtil.matchesRadioState(event)) {
                    return null; // we are already in the updated state - do nothing
                }

                String currentState = event.getParameter(RadioState.PARAMETER_ID);

                // do whatever having "currentState" implies

                // and finally update the current state
                HandlerUtil.updateRadioState(event.getCommand(), currentState);

                //                ICommandService service = (ICommandService) HandlerUtil
                //                                        .getActiveWorkbenchWindowChecked(event).getService(
                //                                            ICommandService.class);
                //                service.refreshElements(event.getCommand().getId(), null);
            } catch (Exception e) {
                utils.topLevelException(shell,this.getClass().getSimpleName(),e);
            }
            return null;
        }
    }

    static public class ClearAllProofResults extends Commands {
        // This is all done in the UI thread with no progress monitor
        @Override
        public Object execute(ExecutionEvent event) {
            try {
                initInfo(event);
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
                initInfo(event);
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
                initInfo(event);
                OpenJMLView.exportProofResults(fw);
            } catch (Exception e) {
                utils.topLevelException(shell,this.getClass().getSimpleName(),e);
            }
            return null;
        }
    }

    static public class ImportProofResults extends Commands {
        @Override
        public Object execute(ExecutionEvent event) {
            try (FileReader fw = new FileReader(new File(System.getProperty("user.home") + "/resultsOutput"))) {
                initInfo(event);
                OpenJMLView.importProofResults(fw);
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
                initInfo(event);

                if (!utils.checkForDirtyEditors()) return null;

                final OpenJMLView view = utils.findView();
                if (view == null || view.selectedList.isEmpty()) return null;

                utils.showView(); // Must be called from a UI thread
                final OpenJMLInterface iface = utils.getInterface(utils.findView().currentProject);
                final IJavaProject jp = iface.jproject;


                final java.util.List<Object> elements = new java.util.LinkedList<>();

                for (TreeItem ti : view.selectedList) {
                    OpenJMLView.Info info = (OpenJMLView.Info)ti.getData();
                    if (info == null) continue;
                    String key = info.key;
                    IJavaElement je = info.javaElement;
                    if (je == null) continue; // FIXME - this can happen if a default constructor is selected - but we should still run on the file
                    elements.add(je);
                }
                String reason = "Rerunning selected items from project " + jp.getResource().getName();

                // The following call launches the actual work in a computational thread
                utils.checkESCProject(jp, elements, shell, reason, null);


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
                initInfo(event);
                // FIXME - iomplement
                utils.showMessageInUI(shell, "OpenJML", "This operation is not yet implemented");
                //utils.changeJmlNatureSelection(true,selection,window,shell);
            } catch (Exception e) {
                utils.topLevelException(shell,this.getClass().getSimpleName(),e);
            }
            return null;
        }
    }

}
