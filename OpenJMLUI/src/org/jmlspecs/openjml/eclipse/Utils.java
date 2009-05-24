package org.jmlspecs.openjml.eclipse;

import java.io.File;
import java.io.InputStream;
import java.io.StringBufferInputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkingSet;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.jmlspecs.annotations.NonNull;
import org.jmlspecs.annotations.Nullable;

public class Utils {

    /** This class is used to wrap arbitrary exceptions coming from OpenJML */
    public static class OpenJMLException extends RuntimeException {
        /** Default serial version ID */
        private static final long serialVersionUID = 1L;

        /** Used to signal some unexpected error situation in doing JML processing. */
        public OpenJMLException(@NonNull String error) {
            super(error);
        }
        /** Used to signal some unexpected error situation in doing JML processing. */
        public OpenJMLException(@NonNull String error, @NonNull Exception e) {
            super(error,e); // FIXME - is e nullable?
        }
    }

    /** This routine initiates (as a Job) checking the JML of all the Java files
     * in the selection; if any containers are selected, the operation applies
     * the contents of the container (including working sets); if any Java 
     * elements are selected (e.g. a method), the operation applies to the
     * containing file.
     * @param selection the current selection (ignored unless it is an IStructuredSelection)
     * @param window null or the currently active IWorkbenchWindow
     * @param shell  the current shell
     */
    public void checkSelection(@NonNull final ISelection selection, @Nullable final IWorkbenchWindow window, @NonNull final Shell shell) {
        final List<IResource> res = getSelectedResources(selection,window,shell);
        if (res.size() == 0) {
            showMessage(shell,"JML Check","Nothing appropriate to check");
            return;
        }
        deleteMarkers(res,shell);
        Job j = new Job("JML Manual Build") {
            public IStatus run(IProgressMonitor monitor) {
                boolean c = false;
                try {
                    ProjectInfo pi = new ProjectInfo(Activator.options,JMLBuilder.preq);
                    (new OpenJMLInterface(pi)).executeExternalCommand(OpenJMLInterface.Cmd.CHECK,res,monitor);
                } catch (Exception e) {
                    showMessageInUI(shell,"OpenJML Exception",e.getClass() + " - " + e.getMessage());
                    c = true;
                }
                return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
            }
        };
        j.setUser(true); // FIXME - document this and elsewhere
        j.schedule();
    }

    /** This routine initiates (as a Job) executing ESC on all the Java files
     * in the selection; if any containers are selected, the operation applies
     * the contents of the container (including working sets).  If a Type or
     * Method is selected, the operation is applied to that element only. (FIXME - not yet)
     * @param selection the current selection (ignored unless it is an IStructuredSelection)
     * @param window null or the currently active IWorkbenchWindow
     * @param shell  the current shell
     */
    public void checkESCSelection(ISelection selection, IWorkbenchWindow window, final Shell shell) {
        final List<Object> res = getSelectedElements(selection,window,shell);
        if (res.size() == 0) {
            showMessage(shell,"ESC","Nothing applicable to check");
            return;
        }
        Log.log("Checking ESC (" + res.size() + " items)");
        deleteMarkers(res,shell);
        Job j = new Job("Static Checks - Manual") {
            public IStatus run(IProgressMonitor monitor) {
                ProjectInfo pi = new ProjectInfo(Activator.options,JMLBuilder.preq);
                boolean c = false;
                try {
                    (new OpenJMLInterface(pi)).executeESCCommand(OpenJMLInterface.Cmd.ESC,res,monitor);
                } catch (Exception e) {
                    String s = e.getMessage();
                    if (s == null || s.length()==0) s = e.getClass().toString();
                    showMessageInUI(shell,"OpenJML",s);
                    c = true;
                }
                return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
            }
        };
        j.setUser(true);
        j.schedule();
    }

    /** This routine initiates (as a Job) compiling RAC for all the Java files
     * in the selection; if any containers are selected, the operation applies
     * the contents of the container (including working sets); if any Java 
     * elements are selected (e.g. a method), the operation applies to the
     * containing file.
     * @param selection the current selection (ignored unless it is an IStructuredSelection)
     * @param window null or the currently active IWorkbenchWindow
     * @param shell  the current shell
     */
    public void racSelection(final ISelection selection, @Nullable final IWorkbenchWindow window, final Shell shell) {
        // For now at least, only IResources are accepted for selection
        final List<IResource> res = getSelectedResources(selection,window,shell);
        if (res.size() == 0) {
            showMessage(shell,"JML RAC","Nothing appropriate to check");
            return;
        }
        Job j = new Job("Compiling Runtime Assertions") {
            public IStatus run(IProgressMonitor monitor) {
                boolean c = false;
                try {
                    ProjectInfo pi = new ProjectInfo(Activator.options,JMLBuilder.preq);
                    (new OpenJMLInterface(pi)).executeExternalCommand(OpenJMLInterface.Cmd.RAC,res,monitor);
                } catch (Exception e) {
                    showMessageInUI(shell,"OpenJML",e.getMessage());
                    c = true;
                }
                return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
            }
        };
        j.setUser(true);
        j.schedule();
    }

    /** This routine initiates (as a Job) generating jmldoc pages for each 
     * project in the selection.  If non-projects are selected, the containing
     * project is used.  For each project, the contents of the source folders
     * are documented.
     * @param selection the current selection (ignored unless it is an IStructuredSelection)
     * @param window null or the currently active IWorkbenchWindow
     * @param shell  the current shell
     */
    public void jmldocSelection(final ISelection selection, @Nullable final IWorkbenchWindow window, final Shell shell) {
        // For now at least, only IResources are accepted for selection
        final List<IResource> res = getSelectedResources(selection,window,shell);
        if (res.size() == 0) {
            showMessage(shell,"JML - jmldoc","Nothing appropriate to check");
            return;
        }
        Job j = new Job("Generating jmldoc") {
            public IStatus run(IProgressMonitor monitor) {
                boolean c = false;
                try {
                    Collection<IJavaProject> projects = getSelectedProjects(false,selection,window,shell);
                    if (projects.size() == 0) projects = getSelectedProjects(true,selection,window,shell);
                    for (IJavaProject p : projects) {
                        ProjectInfo pi = new ProjectInfo(Activator.options,JMLBuilder.preq);
                        (new OpenJMLInterface(pi)).generateJmldoc(p);
                    }
                } catch (Exception e) {
                    showMessageInUI(shell,"OpenJML",e.getMessage());
                    c = true;
                }
                return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
            }
        };
        j.setUser(true);
        j.schedule();
    }

    /** This method pops up an information window to show the specifications of 
     * each selected type, method, or field.  Executed entirely in the UI thread.
     * @param selection the selection (multiple items may be selected)
     * @param window   the current window
     * @param shell    the current shell
     */
    public void showSpecsForSelection(ISelection selection, @Nullable IWorkbenchWindow window, Shell shell) {
        List<Object> list = getSelectedElements(selection, window, shell);
        ProjectInfo pi = null;
        OpenJMLInterface jml = new OpenJMLInterface(pi);
        String sn = "";
        boolean something = false;
        for (Object o : list) {
            try {
                String s = null;
                if (o instanceof IType) {
                    IType t = (IType)o;
                    s = jml.getAllSpecs(t);
                    if (s != null) s = s.replace('\r',' ');
                    sn = "type " + t.getFullyQualifiedName();
                } else if (o instanceof IMethod) {
                    IMethod m = (IMethod)o;
                    s = jml.getAllSpecs(m);
                    if (s != null) s = s.replace('\r',' ');
                    sn = "method " + m.getDeclaringType().getFullyQualifiedName() + "." + m.getElementName();
                } else if (o instanceof IField) {
                    IField f = (IField)o;
                    s = jml.getSpecs(f);
                    if (s != null) s = s.replace('\r',' ');
                    sn = "field " + f.getDeclaringType().getFullyQualifiedName() + "." + f.getElementName();
                }
                if (s != null) {
                    if (s.length()==0) s = "<no specifications>";
                    something = true;
                    showMessageInUINM(shell,"Specifications for " + sn,s);
                } else if (sn != null) {
                    showMessageInUINM(shell,"Specifications","No JML check has been run");
                    return;
                }
            } catch (Exception e) {
                showMessage(shell,"JML", e.getMessage());
            }
        }
        if (!something) showMessage(shell,"JML", "Choose a type, method or field to show specifications");
    }


    /** This method pops up an information window to show the proof result for
     * each selected method.  Executed entirely in the UI thread.
     * @param selection the selection (multiple items may be selected)
     * @param window   the current window
     * @param shell    the current shell
     */
    public void showProofInfoForSelection(ISelection selection, @Nullable IWorkbenchWindow window, Shell shell) {
        List<Object> olist = getSelectedElements(selection, window, shell);
        List<IMethod> list = new LinkedList<IMethod>();
        for (Object o: olist) {
            if (o instanceof IMethod) list.add((IMethod)o);
            // Ignore anything that does not match.  Other types of items can be
            // selected, particularly with a MenuAction.
        }
        ProjectInfo pi = null;
        OpenJMLInterface jml = new OpenJMLInterface(pi);
        if (list.isEmpty()) {
            showMessage(shell,"JML","No methods were selected for the 'show counterexample' operation");
        } else {
            for (IMethod m: list) {
                jml.showProofInfo(m,shell); // This puts up an appropriate dialog 
            }
        }
    }
    /**
     * This method interprets the selection returning a List of IResources or
     * IJavaElements, and
     * ignoring things it does not know how to handle.  The selection is ignored
     * if it is not an IStructuredSelection (e.g. ITextSelections are ignored).
     * If the selection is empty or the resulting list is empty, and 'window'
     * is non-null, then the routine attempts to find a resource that corresponds
     * to the currently active editor.
     * <UL>
     * <LI>IJavaElement - returned in the list
     * <LI>IResource - added directly to list, whether a file or a container
     * <LI>working set - adds the elements of the working set if they can be
     *          converted (through IAdaptor) to an IResource
     * <LI>otherwise - attempts to be converted to an IResource, and added to 
     *          list if successful, ignored otherwise
     * </UL>
     * 
     * @param selection  The selection to inspect
     * @param window  The window in which a selected editor exists, or null
     * @param shell the shell to use in displaying information dialogs, or null
     *      to use a default shell
     * @return A List of IResource or IJavaElement
     */
    public List<Object> getSelectedElements(@NonNull ISelection selection, @NonNull IWorkbenchWindow window, @Nullable Shell shell) {
        List<Object> list = new LinkedList<Object>();
        if (!selection.isEmpty() && selection instanceof IStructuredSelection) {
            IStructuredSelection structuredSelection = (IStructuredSelection) selection;
            for (Iterator iter = structuredSelection.iterator(); iter.hasNext(); ) {
                Object element = iter.next();
                if (element instanceof IJavaElement) {
                    list.add(element);
                } else if (element instanceof IResource) {
                    //Log.log("Selected " + ((IResource)element).getName());
                    list.add(element);
                } else if (element instanceof IWorkingSet) {
                    for (IAdaptable a: ((IWorkingSet)element).getElements()) {
                        IResource r = (IResource) a.getAdapter(IResource.class);
                        if (r != null) list.add(r);
                    }
                    continue;
                } else if (element instanceof IAdaptable) {
                    // TODO: curious as to just what might fall into this category
                    IResource r = ((IResource) ((IAdaptable) element).getAdapter(IResource.class));
                    if (r != null) list.add(r);
                }
            }
        } else {
            // We had nothing selected
            // Look for the active editor instead
            try {
                IEditorPart p = window.getActivePage().getActiveEditor();
                IEditorInput e = p==null? null : p.getEditorInput();
                Object o = e==null ? null : e.getAdapter(IFile.class);
                if (o != null) {
                    //Log.log("Selected " + o);
                    list.add(o);  // This is an IFile
                } 
            } catch (Exception ee) {
                Log.errorlog("Exception when finding selected targets: " + ee,ee);
                showMessage(window.getShell(),"JML Plugin Exception","Exception occurred when finding selected targets: " + ee);
            }
        }
        return list;
    }

    /**
     * This method interprets the selection returning a List of IResources or
     * IJavaElements, and
     * ignoring things it does not know how to handle.  The selection is ignored
     * if it is not an IStructuredSelection (e.g. ITextSelections are ignored).
     * If the selection is empty or the resulting list is empty, and 'window'
     * is non-null, then the routine attempts to find a resource that corresponds
     * to the currently active editor.
     * <UL>
     * <LI>IJavaElement - adds the containing java project
     * <LI>IResource - adds the containing project, as a Java project, if it is one
     * <LI>working set - adds the elements of the working set if they are Java projects
     * <LI>otherwise - attempts to be converted to a IJavaProject or an IResource, 
     *          and added to list if successful, ignored otherwise
     * </UL>
     * @param convert if false, then returned elements were precisely Java Projects
     *      in the selection; if true, the returned projects may also be the 
     *      containing projects of selected non-project elements
     * @param selection  The selection to inspect
     * @param window  The window in which a selected editor exists, or null
     * @param shell the shell to use in displaying information dialogs, or null
     *      to use a default shell
     * @return A List of IResource or IJavaElement
     */
    public Collection<IJavaProject> getSelectedProjects(boolean convert, @NonNull ISelection selection, @NonNull IWorkbenchWindow window, @Nullable Shell shell) {
        Set<IJavaProject> list = new HashSet<IJavaProject>();
        if (!selection.isEmpty()) {
            if (selection instanceof IStructuredSelection) {
                IStructuredSelection structuredSelection = (IStructuredSelection) selection;
                for (Iterator iter = structuredSelection.iterator(); iter.hasNext(); ) {
                    Object element = iter.next();
                    if (!convert) {
                        if (element instanceof IJavaProject) list.add((IJavaProject)element);
                    } else if (element instanceof IJavaElement) {
                        list.add(((IJavaElement)element).getJavaProject());
                    } else if (element instanceof IResource) {
                        IJavaProject jp = JavaCore.create(((IResource)element).getProject());
                        if (jp != null) list.add(jp);
                    } else if (element instanceof IWorkingSet) {
                        for (IAdaptable a: ((IWorkingSet)element).getElements()) {
                            //                            IJavaProject jp = JavaCore.create(((IResource)element).getProject());
                            IJavaProject jp = (IJavaProject)a.getAdapter(IJavaProject.class);
                            if (jp != null) list.add(jp);
                        }
                        continue;
                    } else if (element instanceof IAdaptable) {
                        // TODO: curious as to just what might fall into this category
                        IJavaProject jp = (IJavaProject)((IAdaptable)element).getAdapter(IJavaProject.class);
                        if (jp != null) list.add(jp);
                        else {
                            IResource r = ((IResource) ((IAdaptable) element).getAdapter(IResource.class));
                            jp = JavaCore.create(((IResource)element).getProject());
                            if (r != null) list.add(jp);
                        }
                    }
                }
//            } else {
//                showMessage(shell,"Unknown selection",selection.getClass().toString());
            }
        }
        if (convert && list.size() == 0) {
            // We had nothing selected or it was not a structured selection
            // Look for the active editor instead
            try {
                IEditorPart p = window.getActivePage().getActiveEditor();
                IEditorInput e = p==null? null : p.getEditorInput();
                IFile o = e==null ? null : (IFile)e.getAdapter(IFile.class);
                if (o != null) {
                    IJavaProject jp = JavaCore.create(o.getProject());
                    if (jp != null) list.add(jp);
                } 
            } catch (Exception ee) {
                Log.errorlog("Exception when finding selected targets: " + ee,ee);
                showMessage(window.getShell(),"JML Plugin Exception","Exception occurred when finding selected targets: " + ee);
            }
        }
        return list;
    }

    /**
     * This method interprets the selection returning a List of IResources, and
     * ignoring things it does not know how to handle; note that the resources 
     * in the returned list are not necessarily Java files.  The selection is ignored
     * if it is not an IStructuredSelection (e.g. ITextSelections are ignored).
     * If the selection is empty and 'window'
     * is non-null, then the routine attempts to find a resource that corresponds
     * to the currently active editor.
     * <UL>
     * <LI>IResource - added directly to list, whether a file or a container
     * <LI>working set - adds the elements of the working set if they can be
     *          converted (through IAdaptor) to an IResource
     * <LI>IJavaElement - adds the IResource that contains the element
     * <LI>otherwise - ignored
     * </UL>
     * 
     * @param selection  The selection to inspect
     * @param window  The window in which a selected editor exists
     * @param shell the shell to use in displaying information dialogs
     * @return A List of IResources found in the selection
     */
    public List<IResource> getSelectedResources(@NonNull ISelection selection, 
            @Nullable IWorkbenchWindow window, @Nullable Shell shell) {
        List<IResource> list = new LinkedList<IResource>();
        if (!selection.isEmpty() && selection instanceof IStructuredSelection) {
            IStructuredSelection structuredSelection = (IStructuredSelection) selection;
            for (Iterator iter = structuredSelection.iterator(); iter.hasNext(); ) {
                Object element = iter.next();
                if (element instanceof IResource) {
                    list.add((IResource)element);
                } else if (element instanceof IWorkingSet) {
                    for (IAdaptable a: ((IWorkingSet)element).getElements()) {
                        IResource r = (IResource) a.getAdapter(IResource.class);
                        if (r != null) list.add(r);
                    }
                    continue;
                } else if (element instanceof IJavaElement) {
                    //                    try {
                    IResource r = null;
                    try { r = ((IJavaElement)element).getCorrespondingResource(); } catch (JavaModelException e) { /* ignore */ }
                    if (r != null) list.add(r);
                    else if (element instanceof IAdaptable && (r=(IResource)((IAdaptable)element).getAdapter(IResource.class))!=null) {
                        list.add(r);
                    } else {
                        Log.log("No resource for " + ((IJavaElement)element).getElementName());
                    }
                }
            }
        } else {
            // We had nothing selected
            // Look for the active editor instead
            try {
                IEditorPart p = window.getActivePage().getActiveEditor();
                IEditorInput e = p==null? null : p.getEditorInput();
                IResource o = e==null ? null : (IFile)e.getAdapter(IFile.class);
                if (o != null) {
                    //Log.log("Selected " + o);
                    list.add(o);  // This is an IFile
                } 
            } catch (Exception ee) {
                Log.errorlog("Exception when finding selected targets: " + ee,ee);
                showMessage(shell,"JML Plugin Exception","Exception occurred when finding selected targets: " + ee);
            }
        }
        return list;
    }

    public void changeJmlNatureSelection(boolean enable, ISelection selection, IWorkbenchWindow window, Shell shell) {
        Collection<IJavaProject> list = Activator.getDefault().utils.getSelectedProjects(true,selection,window,shell);
        Iterator<IJavaProject> i = list.iterator();
        if (!i.hasNext()) {
            Activator.getDefault().utils.showMessage(shell,"JML Plugin","No Java projects selected");
            return;
        }
        int maxdialogs = 5;
        while (i.hasNext()) {
            IJavaProject p = i.next();
            try {
                if (enable) JMLNature.enableJMLNature(p.getProject()); // FIXME - do we want to warn about non-java projects in this call , or filter them out beforehand?
                else JMLNature.disableJMLNature(p.getProject()); // FIXME - do we want to warn about non-java projects in this call , or filter them out beforehand?
                PlatformUI.getWorkbench().getDecoratorManager().update(PopupActions.JML_DECORATOR_ID);
            } catch (Exception e) {
                if (window != null && (maxdialogs--) > 0) {
                    Activator.getDefault().utils.showMessage(shell,"JML Plugin Exception",
                            "Exception while " + (enable?"enabling":"disabling") + " JML "
                            + (p != null ? "on " + p.getElementName() : "") +
                            e.toString());
                }           
                Log.errorlog("Failed to " + (enable?"enable":"disable") + " JML nature" +
                        (p!=null? " on project " + p.getElementName() : ""), e);
            }
        }
        Log.log("Completed JML Nature operation ");
    }

    // Do this right here in the UI thread
    // FIXME - should resource things be happening in another thread?
    /** Deletes all JML markers from the items selected, right within the UI thread,
     * without a progress dialog.  The resources for which markers are deleted are
     * those returned by Utils.getSelectedResources.
     * @param selection the IStructuredSelection whose markers are to be deleted
     * @param window the current workbench window, or null (used in getSelectedResources)
     * @param shell the current Shell, or null for the default shell (for message dialogs)
     */
    public void deleteMarkersInSelection(ISelection selection, IWorkbenchWindow window, Shell shell) {
        List<IResource> list = getSelectedResources(selection,window,shell);
        if (list.isEmpty()) {
            showMessage(shell,"JML Plugin","Nothing appropriate to delete markers of");
            return;
        }
        deleteMarkers(list,shell);
        return;
    }
    

    /** This map holds the specs path for each project.  The specs path can hold
     * folders or libraries (jar files).
     */
    Map<IJavaProject, List<File>> specsPaths = new HashMap<IJavaProject, List<File>>();
    
    public void addSelectionToSpecsPath(ISelection selection, IWorkbenchWindow window, Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(false,selection,window,shell);
        if (projects.size() != 1) {
            showMessage(shell,"JML - Add to Specs Path", "Select exactly one Java Project along with the desired folders");
            return;
        }
        IJavaProject jp = projects.iterator().next();
        List<Object> list = getSelectedElements(selection,window,shell);
        List<File> specslist = specsPaths.get(jp);
        if (specslist == null) specsPaths.put(jp, specslist = new LinkedList<File>());
        String notadded = "";
        boolean added = false;
        for (Object r: list) {
            File f;
            if (r instanceof IJavaProject || r instanceof IProject) continue;
            if (r instanceof IPackageFragmentRoot) {
                IPackageFragmentRoot pfr = (IPackageFragmentRoot)r;
                f = pfr.getPath().toFile();
            } else if (r instanceof IFile && "jar".equals(((IFile)r).getFileExtension())) {
                f = ((IFile)r).getLocation().toFile();
            } else if (!(r instanceof IFolder)) {
                notadded = notadded + ((IResource)r).getName() + " " ;
                continue;
            } else {
                f = ((IFolder)r).getLocation().toFile();
            }
            if (specslist.contains(f)) {
                showMessage(shell,"JML - Add to Specs Path","The specs path for " + jp.getElementName() + " already contains " + f);
            } else {
                specslist.add(0,f);
                added = true;
            }
        }
        if (notadded.length()!=0) {
            showMessage(shell,"JML - Add to Specs Path","These were not added: " + notadded);
        } else if (!added) {
            showMessage(shell,"JML - Add to Specs Path","Nothing was added");
        }
    }
    
    public void removeSelectionFromSpecsPath(ISelection selection, IWorkbenchWindow window, Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(false,selection,window,shell);
        if (projects.size() != 1) {
            showMessage(shell,"JML - Remove from Specs Path", "Select exactly one Java Project along with the desired folders");
            return;
        }
        IJavaProject jp = projects.iterator().next();
        List<Object> list = getSelectedElements(selection,window,shell);
        List<File> specslist = specsPaths.get(jp);
        String notremoved = "";
        for (Object r: list) {
            File f; String n;
            if (r instanceof IProject || r instanceof IJavaProject) continue;
            if (r instanceof IPackageFragmentRoot) {
                f =((IPackageFragmentRoot)r).getPath().toFile();
                n = ((IPackageFragmentRoot)r).getElementName();
            } else if (r instanceof IFile && "jar".equals(((IFile)r).getFileExtension())) {
                f = ((IFile)r).getLocation().toFile();
                n = ((IFile)r).getName();
            } else if (r instanceof IFolder) {
                f = ((IFolder)r).getLocation().toFile();
                n = ((IFolder)r).getName();
            } else continue;
            if (specslist == null || !specslist.remove(f)) notremoved = notremoved + n + " ";
        }
        if (notremoved.length()!=0) {
            showMessage(shell,"JML - Remove from Specs Path","These were not removed: " + notremoved);
        }
    }
    
    public void manipulateSpecsPath(ISelection selection, IWorkbenchWindow window, Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(false,selection,window,shell);
        if (projects.size() == 0)  projects = getSelectedProjects(true,selection,window,shell);
        for (IJavaProject jp: projects) {
            List<File> list = specsPaths.get(jp);
            if (list == null) specsPaths.put(jp,list = new LinkedList<File>());
            StringBuilder ss = new StringBuilder();
            for (File s: list) { ss.append(s.toString()); ss.append("\n"); }
            if (!Activator.options.noInternalSpecs) ss.append("<Using internal JML library specs>");
            showMessage(shell,"JML Specs path for project " + jp.getElementName(), ss.toString());
        }
    }
    
    public void manipulateClassPath(ISelection selection, IWorkbenchWindow window, Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(true,selection,window,shell);
        for (IJavaProject jp: projects) {
            List<String> list = getClasspath(jp);
            StringBuilder ss = new StringBuilder();
            for (String s: list) { ss.append(s); ss.append("\n"); }
            showMessage(shell,"JML Classpath for project " + jp.getElementName(), ss.toString());
        }
    }
    
    List<String> getClasspath(IJavaProject jproject) {
        try {
            IClasspathEntry[] entries = jproject.getResolvedClasspath(true); // FIXME - resovled or raw? true or false?
            List<String> cpes = new LinkedList<String>();
            for (IClasspathEntry i: entries) {
                //Log.log("ENTRY " +  i);
                switch (i.getEntryKind()) {
                    case IClasspathEntry.CPE_CONTAINER:
                    case IClasspathEntry.CPE_SOURCE:
                        IResource p = jproject.getProject().getParent().findMember(i.getPath());
                        String s = p.getLocation().toString();
                        //Log.log("E: " + s );
                        cpes.add(s);
                        break;
                    case IClasspathEntry.CPE_LIBRARY:
                        cpes.add(i.getPath().toString());
                        break;
                    case IClasspathEntry.CPE_PROJECT:
                    case IClasspathEntry.CPE_VARIABLE:
                    default:
                        Log.log("CPE NOT HANDLED" + i);
                        break;
                }
            }
            return cpes;
        } catch (JavaModelException e) {
            throw new Utils.OpenJMLException("Failed in determining classpath",e);
        }
    }
    
    public static class StringStorage implements IStorage, IStorageEditorInput {
        private String content;
        private String name;
        public StringStorage(String content, String name) { this.content = content; this.name = name; }
        public InputStream getContents() throws CoreException {
            return new StringBufferInputStream(content);
        }

        public IPath getFullPath() {
            // TODO Auto-generated method stub
            return null;
        }

        public String getName() { return name; }

        public boolean isReadOnly() { return true; }

        public Object getAdapter(Class arg0) { return null; }
        
        public IStorage getStorage() throws CoreException {
            return (IStorage)this;
        }
        public boolean exists() {
            return true;
        }
        public ImageDescriptor getImageDescriptor() {
            return null;
        }
        public IPersistableElement getPersistable() {
            return null;
        }
        public String getToolTipText() {
            return name;
        }

    }

    public void launchEditor(String content,String name) {
        try {
            IEditorInput editorInput = new StringStorage(content,name);
            IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
            IWorkbenchPage page = window.getActivePage();
            
//            IEditorPart[] parts = page.getEditors();
//            for (IEditorPart e: parts) Log.log("EDITOR " + e.getEditorSite().getId());
            page.openEditor(editorInput, "org.eclipse.ui.DefaultTextEditor");
        } catch (Exception e) {
            showMessageInUI(null,"JML Exception",e.getMessage());
            // FIXME
        }

    }
    
    public <T> void deleteMarkers(List<T> list, Shell shell) {
        int maxdialogs = 5;
        for (T t: list) {
            if (!(t instanceof IResource)) continue;
            IResource resource = (IResource)t;
            try {
                try {
                    Log.log("Deleting markers in " + resource.getName());
                    resource.deleteMarkers(JMLBuilder.JML_MARKER_ID, false, IResource.DEPTH_INFINITE);
                } catch (CoreException e) {
                    String msg = "Failed to delete markers on " + resource.getProject();
                    Log.errorlog(msg, e);
                    Activator.getDefault().utils.showMessage(shell,"JML Plugin Exception",msg + " - " + e);
                }
            } catch (Exception e) {
                Log.errorlog("Exception while deleting markers: " + e,e);
                if ((maxdialogs--) > 0) {
                    showMessage(shell,"JML Plugin Exception","Exception while deleting markers "
                            + (resource != null ? "on " + resource.getName() : "") +
                            e.toString());
                }           
            }
        }

    }
    //    /**
    //     * Creates a map indexed by IJavaProject, with the value for
    //     * each IJavaProject being a Collection consisting of the subset
    //     * of the argument that belongs to the Java project.
    //     * 
    //     * @param elements The set of elements to sort
    //     * @return The resulting Map of IJavaProject to Collection
    //     */
    //    /*@ requires elements != null;
    //          requires elements.elementType <: IResource ||
    //                   elements.elementType <: IJavaElement;
    //          ensures \result != null;
    //     */
    //    public static @NonNull <T> Map<IJavaProject,List<T> > sortByProject(@NonNull Collection<T> elements) {
    //        Map<IJavaProject,List<T>> map = new HashMap<IJavaProject,List<T>>();
    //        Iterator<T> i = elements.iterator();
    //        while (i.hasNext()) {
    //            T o = i.next();
    //            IJavaProject jp;
    //            if (o instanceof IResource) {
    //                jp = JavaCore.create(((IResource)o).getProject());
    //            } else if (o instanceof IJavaElement) {
    //                jp = ((IJavaElement)o).getJavaProject();
    //            } else {
    //                Log.errorlog("INTERNAL ERROR: Unexpected content for a selection List - " + o.getClass(),null);
    //                continue;
    //            }
    //            if (jp != null && jp.exists()) addToMap(map,jp,o);
    //        }
    //        return map;
    //    }
    //
    //    /**
    //     * If key is not a key in the map, it is added, with an empty
    //     * Collection for its value; then the given object is added
    //     * to the Collection for that key.
    //     * @param map A map of key values to Collections
    //     * @param key A key value to add to the map, if it is not
    //     *      already present
    //     * @param object An item to add to the Collection for the given key
    //     */
    //    private static <T> void addToMap(@NonNull Map<IJavaProject,List<T>> map, @NonNull IJavaProject key, @NonNull T object) {
    //        List<T> list = map.get(key);
    //        if (list == null) map.put(key, list = new LinkedList<T>());
    //        list.add(object);
    //    }

    /**
     * Displays a message in a dialog in the UI thread - this may
     * be called from other threads.
     * @param sh  The shell to use to display the dialog, or 
     *      a top-level shell if the parameter is null
     * @param title  The title of the dialog window
     * @param msg  The message to display in the dialog
     */
    public void showMessageInUI(@Nullable Shell sh, 
            @NonNull final String title, @NonNull final String msg) {
        final Shell shell = sh;
        Display d = shell == null ? Display.getDefault() : shell.getDisplay();
        d.asyncExec(new Runnable() {
            public void run() {
                MessageDialog.openInformation(
                        shell,
                        title,
                        msg);
            }
        });
    }

    /**
     * Displays a message in a dialog in the UI thread - this may
     * be called from other threads.
     * @param sh  The shell to use to display the dialog, or 
     *      a top-level shell if the parameter is null
     * @param title  The title of the dialog window
     * @param msg  The message to display in the dialog
     */
    public void showMessageInUINM(@Nullable Shell sh, 
            @NonNull final String title, @NonNull final String msg) {
        final Shell shell = sh;
        Display d = shell == null ? Display.getDefault() : shell.getDisplay();
        d.asyncExec(new Runnable() {
            public void run() {
                Dialog d = new NonModalDialog(
                        shell,
                        title,
                        msg);
                d.open();
            }
        });
    }

    static public class NonModalDialog extends MessageDialog {
        final static String[] buttons = { "OK" };
        public NonModalDialog(Shell shell, String title, String message) {
            super(new Shell(),title,null,message,INFORMATION,buttons,0);
            setShellStyle(getShellStyle()|SWT.MODELESS);
            setBlockOnOpen(false);
        }
    }

    /**
     * Displays a message in a information dialog; must be called from the UI thread.
     * @param shell  Either the parent shell
     * @param title  A title for the dialog window
     * @param msg   The message to display in the dialog window
     */
    //@ requires shell != null;
    //@ requires title != null;
    //@ requires msg != null;
    public void showMessage(Shell shell, String title, String msg) {
        MessageDialog.openInformation(
                shell,
                title,
                msg);
    }
    
    public void topLevelException(Shell shell, String title, Exception e) {
        //e.printStackTrace(sw); // FIXME
        showMessage(shell,"JML Top-level Exception: " + title,
                e.toString());
    }
}
