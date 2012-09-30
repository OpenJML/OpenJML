/*
 * This file is part of the OpenJML plugin project. 
 * Copyright (c) 2006-2010 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileWriter;
import java.io.InputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IStorage;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.Flags;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.ITypeHierarchy;
import org.eclipse.jdt.core.ITypeParameter;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkingSet;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.annotation.Query;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.osgi.framework.Bundle;

// FIXME - review UI Utils class

/** This class holds utility values and methods to support the Eclipse plugin
 * for OpenJML.
 * 
 * @author David Cok
 *
 */
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
            super(error,e);
        }
    }

    /** The ID of the marker, which must match that in the plugin file. */
    final public static @NonNull String JML_MARKER_ID = Activator.PLUGIN_ID + ".JMLProblem";

    /** The ID of the marker, which must match that in the plugin file. */
    final public static @NonNull String JML_HIGHLIGHT_ID = Activator.PLUGIN_ID + ".JMLHighlight";

    /** The ID of the marker, which must match that in the plugin file. */
    final public static @NonNull String ESC_MARKER_ID = Activator.PLUGIN_ID + ".JMLESCProblem";

    /** A map relating java projects to the instance of OpenJMLInterface that
     * handles openjml stuff for that project.  we have a separate instance for
     * each project since options can be different by project.
     */
    final
    protected @NonNull Map<IJavaProject,OpenJMLInterface> projectMap = new HashMap<IJavaProject,OpenJMLInterface>();

    /** Returns the unique OpenJMLInterface for a given project
     * @param jproject the Java project whose interface is desired
     * @return the OpenJMLInterface for that project
     */
    public @NonNull OpenJMLInterface getInterface(@NonNull IJavaProject jproject) {
    	readProjectProperties(jproject.getProject());
        OpenJMLInterface i = projectMap.get(jproject);
        if (i == null) {
            projectMap.put(jproject, i = new OpenJMLInterface(jproject));
        }
        return i;
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
        List<IResource> res = getSelectedResources(selection,window,shell);
        if (res.size() == 0) {
            showMessage(shell,"JML Check","Nothing appropriate to check");
            return;
        }
        deleteMarkers(res,shell);
        final Map<IJavaProject,List<IResource>> sorted = sortByProject(res);
        for (final IJavaProject jp : sorted.keySet()) {
			if (Activator.options.autoAddRuntimeToProject) addRuntimeToProjectClasspath(jp);
            final List<IResource> ores = sorted.get(jp);
            Job j = new Job("JML Manual Check") {
                public IStatus run(IProgressMonitor monitor) {
                    boolean c = false;
                    try {
                        getInterface(jp).executeExternalCommand(OpenJMLInterface.Cmd.CHECK,ores,monitor);
                    } catch (Exception e) {
                        showExceptionInUI(shell,e);
                        c = true;
                    }
                    return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
                }
            };
            j.setUser(true); // true since the job has been initiated by an end-user
            j.schedule();
        }
    }

    /** This routine initiates (as a Job) executing ESC on all the Java files
     * in the selection; if any containers are selected, the operation applies
     * the contents of the container (including working sets).  If a Type or
     * Method is selected, the operation is applied to that element only. (FIXME - not yet)
     * @param selection the current selection (ignored unless it is an IStructuredSelection)
     * @param window null or the currently active IWorkbenchWindow
     * @param shell  the current shell
     */
    public void checkESCSelection(ISelection selection, @Nullable IWorkbenchWindow window, @Nullable final Shell shell) {
        final List<Object> res = getSelectedElements(selection,window,shell);
        if (res.size() == 0) {
            showMessage(shell,"ESC","Nothing applicable to check");
            return;
        }
        final Map<IJavaProject,List<Object>> sorted = sortByProject(res);
        for (final IJavaProject jp : sorted.keySet()) {
			if (Activator.options.autoAddRuntimeToProject) addRuntimeToProjectClasspath(jp);
            final List<Object> ores = sorted.get(jp);
            if (Activator.options.uiverbosity >= 2) Log.log("Checking ESC (" + res.size() + " items)");
            deleteMarkers(res,shell);
            Job j = new Job("Static Checks - Manual") {
                public IStatus run(IProgressMonitor monitor) {
                    boolean c = false;
                    try {
                        getInterface(jp).executeESCCommand(OpenJMLInterface.Cmd.ESC,
                                        ores,monitor);
                    } catch (Exception e) {
                        showExceptionInUI(shell,e);
                        c = true;
                    }
                    return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
                }
            };
            j.setUser(true); // true since the job has been initiated by an end-user
            j.schedule();
        }
    }
    
    static public void readProperties() {
    	// FIXME - as different projects are processed, they continually overwrite each other's properties
    	//Log.log("About to read properties");
        java.util.Properties properties = new java.util.Properties();
        {
        	// Note: It appears that a file in the workspace root is not seen as
        	// a member of the workspace - just projects - because findMember on
        	// the workspace root returns null. So we find the file directly in
        	// the local file system.
        	IPath path = ResourcesPlugin.getWorkspace().getRoot().getLocation().append(org.jmlspecs.openjml.Utils.propertiesFileName);
        	boolean found = org.jmlspecs.openjml.Utils.readProps(properties,path.toFile().getAbsolutePath());
            if (found) Log.log("Properties read from the workspace: " + path.toOSString());
        }
        System.getProperties().putAll(properties);
    }

    public void readProjectProperties(IProject project) {
    	// FIXME - as different projects are processed, they continually overwrite each other's properties
    	//Log.log("About to read properties");
    	readProperties();
        java.util.Properties properties = new java.util.Properties();
        {
        	//Log.log("Project location: " + project.getLocation());
            IResource res = project.findMember(org.jmlspecs.openjml.Utils.propertiesFileName);
            if (res != null) {
            	boolean found = org.jmlspecs.openjml.Utils.readProps(properties,res.getLocation().toOSString());
                if (found && Activator.options.uiverbosity >= 1) Log.log("Properties read from the project directory: " + res.getLocation().toOSString());
            }
        }
        System.getProperties().putAll(properties);
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
    public void racSelection(final @NonNull ISelection selection, @Nullable final IWorkbenchWindow window, final Shell shell) {
        // For now at least, only IResources are accepted for selection
        final @NonNull List<IResource> res = getSelectedResources(selection,window,shell);
        if (res.size() == 0) {
            showMessage(shell,"JML RAC","Nothing appropriate to check");
            return;
        }
        final @NonNull Map<IJavaProject,List<IResource>> sorted = sortByProject(res);
        for (final IJavaProject jp : sorted.keySet()) {
            Job j = new Job("Compiling Runtime Assertions") {
                public IStatus run(IProgressMonitor monitor) {
                    boolean c = false;
                    try {
                        getInterface(jp).executeExternalCommand(OpenJMLInterface.Cmd.RAC,sorted.get(jp),monitor);
                    } catch (Exception e) {
                        showExceptionInUI(shell,e);
                        c = true;
                    }
                    return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
                }
            };
            j.setUser(true); // true since the job has been initiated by an end-user
            j.schedule();
        }
    }
    
    // TODO - document doBuildRac - put in a Job - or not - because called from a computation thread anyway
    protected void doBuildRac(IJavaProject jproject, List<IResource> resourcesToBuild, IProgressMonitor monitor) {
        Set<IResource> enabledForRac = getSet(jproject);
        List<IResource> newlist = new ArrayList<IResource>(enabledForRac.size());
        for (IResource r: resourcesToBuild) {
            if (enabledForRac.contains(r)) newlist.add(r);
        }
        if (newlist.size() != 0) {
            try {
            	if (Activator.options.uiverbosity >= 2) Log.log("Starting RAC " + newlist.size() + " files");
                getInterface(jproject).executeExternalCommand(OpenJMLInterface.Cmd.RAC,newlist,monitor);
                if (Activator.options.uiverbosity >= 2) Log.log("Completed RAC");
            } catch (Exception e) {
                showExceptionInUI(null,e);
            }
        } else {
        	if (Activator.options.uiverbosity >= 2) Log.log("Nothing to RAC");
        }
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
                        getInterface(p).generateJmldoc(p);
                    }
                } catch (Exception e) {
                    showExceptionInUI(shell,e);
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
        String sn = "";
        boolean something = false;
        for (Object o : list) {
            try {
                String s = null;
                if (o instanceof IType) {
                    IType t = (IType)o;
                    s = getInterface(t.getJavaProject()).getAllSpecs(t);
                    if (s != null) s = s.replace('\r',' ');
                    sn = "type " + t.getFullyQualifiedName();
                } else if (o instanceof IMethod) {
                    IMethod m = (IMethod)o;
                    s = getInterface(m.getJavaProject()).getAllSpecs(m);
                    if (s != null) s = s.replace('\r',' ');
                    sn = "method " + m.getDeclaringType().getFullyQualifiedName() + "." + m.getElementName();
                } else if (o instanceof IField) {
                    IField f = (IField)o;
                    s = getInterface(f.getJavaProject()).getSpecs(f);
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
        if (!something) showMessage(shell,"JML", "Choose a type, method or field whose specifications are to be shown");
    }
    
    /** This method opens an editor on the specs for the selected Java classes.  
     * Executed entirely in the UI thread.
     * @param selection the selection (multiple items may be selected)
     * @param window   the current window
     * @param shell    the current shell
     */
    public void openSpecEditorForSelection(ISelection selection, @Nullable IWorkbenchWindow window, Shell shell) {
        ITextSelection textSelection = getSelectedText(selection);
        List<Object> list;
        String text;
        if (textSelection != null && window != null && (text=textSelection.getText()).length() != 0) {
        	if (Activator.options.uiverbosity >= 2) Log.log("Selected text: " + text);
            String classname = text.replace('.','/') + ".class";
            IEditorPart p = window.getActivePage().getActiveEditor();
            IEditorInput e = p==null? null : p.getEditorInput();
            IFile o = e==null ? null : (IFile)e.getAdapter(IFile.class);
            IJavaProject jp = o == null ? null : JavaCore.create(o).getJavaProject();
            List<IType> matches = new LinkedList<IType>();
            if (jp != null) try {
                for (IClasspathEntry cpe: jp.getResolvedClasspath(true)) {
                    //Log.log(" CPE " + cpe);  // cpe is SOURCE, PROJECT, or LIBRARY
                    if (cpe.getEntryKind() == IClasspathEntry.CPE_LIBRARY) {
                        // findPackageFragmentRoots does not work for library entries
                        try {
                            ZipFile z = new ZipFile(cpe.getPath().toString());
                            Enumeration<? extends ZipEntry> en = z.entries();
                            while (en.hasMoreElements()) {
                                ZipEntry ze = en.nextElement();
                                String zs = ze.getName();
                                if (zs.endsWith(classname)) {
                                    zs = zs.replace('/','.');
                                    zs = zs.substring(0,zs.length()-".class".length());
                                    matches.add(jp.findType(zs));
                                }
                            }
                            z.close();
                        } catch (java.io.IOException ex) {
                            Log.errorlog("Failed to open jar file " + cpe.getPath().toString(),ex);
                            // Pretend there is no match
                        }
                    } else {
                        for (IPackageFragmentRoot pfr: jp.findPackageFragmentRoots(cpe)) {
                            //Log.log("  PackageFragmentRoot " + pfr.isOpen() + " " + pfr.getElementName());
                            if (!pfr.isOpen()) continue;
                            for (IJavaElement element : pfr.getChildren()) { // element is a IPackageFragment
                                //Log.log("    Package " + element.getElementName());
                                for (IJavaElement je: ((IPackageFragment)element).getChildren()) { // je is a ICompilationUnit
                                    //Log.log("      CompUnit " + je.getElementName());
                                    if (je instanceof ICompilationUnit) for (IType ee: ((ICompilationUnit)je).getAllTypes()) {
                                        //Log.log("        Type " + ee.getElementName());
                                        if (ee.getFullyQualifiedName().endsWith(text)) {
                                            matches.add(ee);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            } catch (JavaModelException ex) {
                Log.errorlog("Failed to match text to a type name because of an exception",ex);
                // Pretend there is no match
            }
            list = new LinkedList<Object>();
            if (matches.size() == 1) {
                list.add(matches.get(0));
            } else if (matches.size() > 1) {
                IType fullmatch = null;
                IType partialmatch = null;
                String ptext = "." + text;
                for (IType t: matches) {
                    String fqname = t.getFullyQualifiedName();
                    if (fqname.equals(text)) {
                        fullmatch = t;
                        list.add(fullmatch);
                        break;
                    }
                    if (fqname.endsWith(ptext)) {
                        partialmatch = t;
                    }
                }
                if (fullmatch == null) {
                    if (partialmatch != null) list.add(partialmatch);
                    else list.add(matches.get(0));
                }
                // FIXME we are just using the first match and ignoring any others
                // - should we ask the user which to use
                // - even better is to get the class from the resolved AST directly so we get it correct
                // (but we also want to do that for stuff in specs)
            }
        } else {
            list = getSelectedElements(selection, window, shell);
        }
        boolean something = false;
        String kinds = "";
        for (Object o : list) {
            try {
                IType t = null;
                if (o instanceof IType) {
                    t = (IType)o;
                } else if (o instanceof ICompilationUnit) {
                    t = ((ICompilationUnit)o).findPrimaryType();
                } else if (o instanceof IFile) {
                    IJavaElement cu = JavaCore.create((IFile)o);
                    if (cu instanceof ICompilationUnit) t = ((ICompilationUnit)cu).findPrimaryType();
                } else if (o instanceof IAdaptable) {
                    ICompilationUnit cu = (ICompilationUnit)((IAdaptable)o).getAdapter(ICompilationUnit.class);
                    if (cu != null) t = cu.findPrimaryType();
                    if (t == null) t = (IType)((IAdaptable)o).getAdapter(IType.class);
                } 
                if (t == null) {
                    kinds = kinds + o.getClass() + " ";
                    continue;
                }
                String name = t.getElementName();
                String[] fullnames = new String[suffixes.length];
                for (int i=0; i<suffixes.length; i++) fullnames[i] = name + suffixes[i];
                String pname = t.getPackageFragment().getElementName();
                pname = pname.replace('.','/');
                List<IResource> roots = getInterface(t.getJavaProject()).specsPath;
                IFolder firstEditableLocation = null;
                IFile match = null;
                ZipFile jarfile = null;
                ZipEntry jarentry = null;
                outer: for (IResource f: roots) {
                    if (f instanceof IFolder) {
                        IResource ff = ((IFolder)f).findMember(pname);
                        if (ff == null || !ff.exists() || !(ff instanceof IFolder)) continue;
                        if (firstEditableLocation == null) firstEditableLocation = (IFolder)ff;
                        for (String n: fullnames) {
                            IResource fff = ((IFolder)ff).findMember(n);
                            if (fff != null && fff.exists() && fff instanceof IFile) { 
                                match = (IFile)fff; 
                                break outer; 
                            }
                        }
                    } else { // Jar file
                        ZipFile jf = new ZipFile(f.getLocation().toString());
                        ZipEntry je = jf.getEntry(pname);
                        if (je != null) {
                            for (String n: fullnames) {
                                ZipEntry nje = jf.getEntry(pname + "/" + n);
                                if (nje != null) { 
                                    jarfile = jf;
                                    jarentry = nje; 
                                    break outer; 
                                }
                            }
                        }
                        jf.close();
                    }
                }
                something = true;
                if (match != null) {
                    launchJavaEditor(match);
                } else if (jarentry != null) {
                    InputStream is = jarfile.getInputStream(jarentry);
                    int size = (int)jarentry.getSize();
                    byte[] bytes = new byte[size];
                    is.read(bytes,0,size);
                    String s = new String(bytes);
                    showMessage(shell,"JML - Spec Editor","Specification file for " + t.getFullyQualifiedName() + " in " + jarfile.getName() + " is read-only");
                    String nm = jarentry.getName();
                    int k = nm.lastIndexOf('/');
                    if (k >= 0) nm = nm.substring(k+1);
                    launchJavaEditor(s,nm);
                } else if (firstEditableLocation != null) {
                    IFile newfile = firstEditableLocation.getFile(name + ".jml");
                    if (Activator.options.uiverbosity >= 2) Log.log("Creating " + newfile);
                    // FIXME - add default content
                    // FIXME - be able to decline to create, or to choose location
                    boolean b = MessageDialog.openConfirm(
                            shell,"JML - Specs Editor","Creating " + newfile);
                    if (b) {
                        PrintWriter w = new PrintWriter(new FileWriter(newfile.getLocation().toString()));
                        generateDefaultSpecs(w,t);
                        newfile.refreshLocal(IResource.DEPTH_ZERO,null);
                        launchJavaEditor(newfile);
                    }

                } else {
                    showMessage(shell,"JML", "No spec file or possible new location found " + t.getFullyQualifiedName());
                }
            } catch (Exception e) {
                showMessage(shell,"JML", "Internal Error: " + e);
            }
        }
        if (!something) {
            showMessage(shell,"JML - no specs files",
                    kinds.length() == 0 ? "Nothing found for which to open an editor"
                            : "Cannot show specification files for " + kinds);
        }
    }
    
    // FIXME - add default content - document

    public void generateDefaultSpecs(PrintWriter ww, IType t) {
        StringWriter sw = new StringWriter();
        PrintWriter w = new PrintWriter(sw);
        Set<String> imports = new HashSet<String>();
        try {
            // No extending Object
            // No importing java.lang
            // No duplicate imports
            // type parameters names and bounds not handled correctly
            // Need methods and fields and nested classes
            // Need secondary types
            printClass(w,t,imports);
        } catch (JavaModelException e) {
            w.println("<Error in generating default content>");
        }
        w.close();
        ww.println("package " + t.getPackageFragment().getElementName() + ";");
        for (String s: imports) {
            ww.println("import " + s + ";");
        }
        ww.println();
        ww.println(sw.toString());
        ww.close();
    }
    
    // FIXME - document
    protected void printClass(PrintWriter w, IType t, Set<String> imports) throws JavaModelException {
        ITypeHierarchy th = t.newSupertypeHierarchy(null);
        IType sup = th.getSuperclass(t);
        if (sup.getFullyQualifiedName().equals("java.lang.Object")) sup = null;
        IType[] ifaces = th.getSuperInterfaces(t);
        if (sup != null) imports.add(sup.getPackageFragment().getElementName());
        for (IType i: ifaces) imports.add(i.getPackageFragment().getElementName());
        w.println();
        // FIXME - annotations
        w.print(Flags.toString(t.getFlags()));
        w.print(" class " );
        printType(w,t,imports);
        if (sup != null) {
            w.print(" extends ");
            printType(w,sup,imports);
        }
        if (ifaces.length > 0) w.print(" implements");
        boolean isFirst = true;
        for (IType i: ifaces) {
            if (isFirst) isFirst = false; else w.print(",");
            w.print(" ");
            printType(w,i,imports);
        }
        w.println(" {");
        w.println();
//        w.println("  //@ requires true;");
//        w.println("  //@ ensures true;");
//        w.println("  //@ static_initalizer;");
//        w.println();
//        w.println("  //@ requires true;");
//        w.println("  //@ ensures true;");
//        w.println("  //@ initalizer;");
//        
//        for (IMethod m : t.getMethods()) {
//            w.println();
//            w.print("    ");
//            // FIXME - annotations
//            w.print(Flags.toString(m.getFlags()));
//            w.print(" ");
//            w.print(m.getReturnType());
//            w.print(" ");
//            w.print(m.getElementName());
//            w.print("(");
//            boolean isFirst2 = true;
//            String[] pn = m.getParameterNames();
//            String[] pt = m.getParameterTypes();
//            for (int i=0; i<pn.length; i++) {
//                if (isFirst2) isFirst2 = false; else w.print(", ");
//                // FIXME _ modifierse
//                w.print(pt[i]);
//                w.print(" ");
//                w.print(pn[i]);
//            }
//            w.print(")");
//            // FIXME - exceptions
//            w.print(";");
//        }
        w.println();
        w.println("}");
    }
    
    // FIXME - document
    protected void printType(PrintWriter w, IType t, Set<String> imports) throws JavaModelException {
        w.print(t.getElementName());
        ITypeParameter[] tparams = t.getTypeParameters();
        if (tparams.length != 0) {
            w.print("<");
            boolean isFirst = true;
            for (ITypeParameter tp: tparams) {
                if (isFirst) isFirst = false; else w.print(",");
                w.print(tp.getElementName());
                String[] bounds = tp.getBounds();
                if (bounds.length > 0) {
                    w.print(" extends");
                    boolean isFirst2 = true;
                    for (String s: bounds) {
                        if (isFirst2) isFirst2 = false; else w.print(" &");
                        w.print(" ");
                        w.print(s);
                    }
                }
            }
            w.print(">");
        }
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
        if (list.isEmpty()) {
            showMessage(shell,"JML","No methods were selected for the 'show proof info' operation");
        } else {
            for (IMethod m: list) {
                OpenJMLInterface jml = getInterface(m.getJavaProject());
                jml.showProofInfo(m,shell); // This puts up an appropriate dialog 
            }
        }
    }
    
    /** This method pops up an information window to show the value of an 
     * expression in the current counterexample.  Uses the computational
     * thread.
     * @param selection the selection (multiple items may be selected)
     * @param window   the current window
     * @param shell    the current shell
     */
    public void showCEValueForTextSelection(ISelection selection, @Nullable IWorkbenchWindow window, Shell shell) {
        ITextSelection selectedText = getSelectedText(selection);
        if (selectedText == null) {
            showMessage(shell,"JML","No text is selected");
            return;
        }
        int pos = selectedText.getOffset();
        int end = pos + selectedText.getLength() - 1;
        if (end < pos) {
            showMessage(shell,"JML","No text is selected");
            return;
        }
        String s = selectedText.getText();
        //showMessage(shell,"JML",pos + " " + end + " " + "Selected " + s);
        IResource r = getSelectedResources(selection,window,shell).get(0);
        // FIXME - need to do this in another thread. ?
        String result = getInterface(JavaCore.create(r.getProject())).getCEValue(pos,end,s,r);
        showMessage(shell,"Counterexample value",result);
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
            for (Iterator<?> iter = structuredSelection.iterator(); iter.hasNext(); ) {
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
                Object o = e==null ? null : e.getAdapter(ICompilationUnit.class);
                o = o==null ? e.getAdapter(IFile.class) : o;
                o = o==null? e : o;
                if (o != null) {
                    //Log.log("Selected " + o);
                    list.add(o);
                } 
            } catch (Exception ee) {
                Log.errorlog("Exception when finding selected targets: " + ee,ee);
                showMessage(window.getShell(),"JML Plugin Exception","Exception occurred when finding selected targets: " + ee);
            }
        }
        return list;
    }

    // TODO - document
    public ITextSelection getSelectedText(@NonNull ISelection selection) {
        if (!selection.isEmpty() && selection instanceof ITextSelection) {
            return (ITextSelection)selection;
        } else {
            return null;
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
                for (Iterator<?> iter = structuredSelection.iterator(); iter.hasNext(); ) {
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
            for (Iterator<?> iter = structuredSelection.iterator(); iter.hasNext(); ) {
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
                    	if (Activator.options.uiverbosity >= 2) Log.log("No resource for " + ((IJavaElement)element).getElementName());
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

    /** Alters whether the JML nature is enabled or disabled for the given
     * selected objects.  The operation makes sense only for IJavaProject objects;
     * if other types of objects are selected, the enclosing IJavaProject is
     * used; if there is none, the selected object is ignored.   The operation is
     * performed entirely in the UI thread (and should be called from the UI thread).
     * @param enable if true, the JML nature is enabled; if false, it is disabled
     * @param selection the objects selected in the UI
     * @param window the current window
     * @param shell the current shell (for any dialogs)
     */
    public void changeJmlNatureSelection(boolean enable, ISelection selection, IWorkbenchWindow window, Shell shell) {
        Collection<IJavaProject> list = Activator.getDefault().utils.getSelectedProjects(true,selection,window,shell);
        Iterator<IJavaProject> i = list.iterator();
        if (!i.hasNext()) {
            Utils.showMessage(shell,"JML Plugin","No Java projects selected");
            return;
        }
        int maxdialogs = 5;
        while (i.hasNext()) {
            IJavaProject p = i.next();
            try {
                if (enable) JMLNature.enableJMLNature(p.getProject());
                else JMLNature.disableJMLNature(p.getProject());
                PlatformUI.getWorkbench().getDecoratorManager().update(PopupActions.JML_DECORATOR_ID);
            } catch (Exception e) {
                if (window != null && (maxdialogs--) > 0) {
                    Utils.showMessage(shell,"JML Plugin Exception",
                            "Exception while " + (enable?"enabling":"disabling") + " JML "
                            + (p != null ? "on " + p.getElementName() : "") +
                            e.toString());
                }           
                Log.errorlog("Failed to " + (enable?"enable":"disable") + " JML nature" +
                        (p!=null? " on project " + p.getElementName() : ""), e);
            }
        }
        if (Activator.options.uiverbosity >= 2) Log.log("Completed JML Nature operation ");
    }

    // Do this right here in the UI thread
    // FIXME - should resource things be happening in another thread?
    /** Deletes all JML markers from the items selected, right within the UI thread,
     * without a progress dialog.  The resources for which markers are deleted are
     * those returned by Utils.getSelectedResources.   This should be called from
     * the UI thread.
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


    /** Expects the selection to hold exactly one Java project, plus one or more
     * folders or jar files; those folders and jar files are added to the 
     * beginning of the specs path for the given project.
     * @param selection the current selection in the UI
     * @param window the currently active window
     * @param shell the current shell (for dialogs)
     */
    public void addSelectionToSpecsPath(ISelection selection, IWorkbenchWindow window, @Nullable Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(false,selection,window,shell);
        if (projects.size() != 1) {
            showMessage(shell,"JML - Add to Specs Path", "Select exactly one Java Project along with the desired folders");
            return;
        }
        IJavaProject jp = projects.iterator().next();
        List<Object> list = getSelectedElements(selection,window,shell);
        String notadded = "";
        boolean added = false;
        for (Object r: list) {
            IResource f;
            if (r instanceof IJavaProject || r instanceof IProject) continue;
            if (r instanceof IPackageFragmentRoot) {
                IPackageFragmentRoot pfr = (IPackageFragmentRoot)r;
                f = pfr.getResource();
            } else if (r instanceof IFile && "jar".equals(((IFile)r).getFileExtension())) {
                f = (IFile)r;
            } else if (!(r instanceof IFolder)) {
                notadded = notadded + ((IResource)r).getName() + " " ;
                continue;
            } else {
                f = (IFolder)r;
            }
            List<IResource> specsPath = getInterface(jp).specsPath;
            if (specsPath.contains(f)) {
                showMessage(shell,"JML - Add to Specs Path","The specs path for " + jp.getElementName() + " already contains " + f);
            } else {
                specsPath.add(0,f);
                putSpecsPath(jp,specsPath);
                added = true;
            }
        }
        if (notadded.length()!=0) {
            showMessage(shell,"JML - Add to Specs Path","These were not added: " + notadded);
        } else if (!added) {
            showMessage(shell,"JML - Add to Specs Path","Nothing was added");
        }
    }

    /** Expects the selection to hold exactly one Java project, plus one or more
     * folders or jar files; those folders and jar files are removed from the 
     * the specs path of the given project.
     * @param selection the current selection in the UI
     * @param window the currently active window
     * @param shell the current shell (for dialogs)
     */
    public void removeSelectionFromSpecsPath(ISelection selection, @Nullable IWorkbenchWindow window, @Nullable Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(false,selection,window,shell);
        if (projects.size() != 1) {
            showMessage(shell,"JML - Remove from Specs Path", "Select exactly one Java Project along with the desired folders");
            return;
        }
        IJavaProject jp = projects.iterator().next();
        List<Object> list = getSelectedElements(selection,window,shell);
        List<IResource> specsPath = getInterface(jp).specsPath;
        String notremoved = "";
        for (Object r: list) {
            IResource f; String n;
            if (r instanceof IProject || r instanceof IJavaProject) continue;
            if (r instanceof IPackageFragmentRoot) {
                f = (IResource)r;
                n = ((IPackageFragmentRoot)r).getElementName();
            } else if (r instanceof IFile && "jar".equals(((IFile)r).getFileExtension())) {
                f = (IFile)r;
                n = ((IFile)r).getName();
            } else if (r instanceof IFolder) {
                f = (IFolder)r;
                n = ((IFolder)r).getName();
            } else continue;
            if (!specsPath.remove(f)) notremoved = notremoved + n + " ";
        }
        if (notremoved.length()!=0) {
            showMessage(shell,"JML - Remove from Specs Path","These were not removed: " + notremoved);
        }
        putSpecsPath(jp,specsPath);
    }

    // TODO _ document; also clarify the content
    public void manipulateSpecsPath(ISelection selection, IWorkbenchWindow window, Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(false,selection,window,shell);
        if (projects.size() == 0)  projects = getSelectedProjects(true,selection,window,shell);
        for (IJavaProject jp: projects) {
            List<IResource> list = getInterface(jp).specsPath;
//            StringBuilder ss = new StringBuilder();
//            for (IFile s: list) { ss.append(s.toString()); ss.append("\n"); }
//            if (!Activator.options.noInternalSpecs) ss.append("<Using internal JML library specs>\n");
//            ss.append("----------------\n");
//            List<String> pdirs = getInterface(jp).getSpecsPath();
//            for (String s: pdirs) { ss.append(s); ss.append("\n"); }
            //showMessage(shell,"JML Specs path for project " + jp.getElementName(), ss.toString());
            Dialog d = new SpecsPathEditor(shell,jp,list);
            d.open();
            if (d.getReturnCode() == Dialog.OK) {
                // Save the altered items to persistent storage
                putSpecsPath(jp,list);
                Preferences.poptions.noInternalSpecs.setValue(Activator.options.noInternalSpecs);
            }
        }
    }

    /** Shows the classpath for selected projects.  
     * SHould be called from the UI thread; is executed entirely in the calling thread.
     * @param selection the current selection in the UI
     * @param window the currently active window
     * @param shell the currently active shell (or null for default)
     */
    public void manipulateClassPath(ISelection selection, IWorkbenchWindow window, Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(true,selection,window,shell);
        for (IJavaProject jp: projects) {
            List<String> list = getClasspath(jp);
            StringBuilder ss = new StringBuilder();
            for (String s: list) { ss.append(s); ss.append("\n"); }
            showMessage(shell,"JML Classpath for project " + jp.getElementName(), ss.toString());
        }
    }
    
    private boolean changingClasspath = false;
    
    /** Adds a Library classpath entry holding the internal run-time library
     * to the end of the given project's classpath, if the library is not already
     * on the classpath. This will trigger a build, if auto-building is turned on.
     * @param jproject the project whose classpath is to be adjusted
     */
    public void addRuntimeToProjectClasspath(IJavaProject jproject) {
    	if (changingClasspath) return;
    	try {
    		String runtime = findInternalRuntime();
    		if (runtime == null) return;
    		IPath path = new Path(runtime);
    		IClasspathEntry libentry = JavaCore.newLibraryEntry(path,null,null);

    		IClasspathEntry[] entries = jproject.getResolvedClasspath(true);
    		for (IClasspathEntry i: entries) {
    			if (i.getEntryKind() == IClasspathEntry.CPE_LIBRARY
    					&& i.equals(libentry)) return;
    		}
    		IClasspathEntry[] newentries = new IClasspathEntry[entries.length+1];
    		System.arraycopy(entries,0,newentries,0,entries.length);
    		newentries[entries.length] = libentry;
    		try {
    			changingClasspath = true;
    			// TODO - should this be in a computational thread
    			jproject.setRawClasspath(newentries,null); // TODO _ no monitor? might recompile
    		} finally {
    			changingClasspath = false;
    		}
    	} catch (JavaModelException e) {
    		throw new Utils.OpenJMLException("Failed in adding internal runtime library to classpath: " + e.getMessage(),e);
    	}
    }

    /** Gets the classpath of the given project, interpreting all Eclipse entries
     * and converting them into file system paths to directories or jars.
     * @param jproject the Java project whose class path is wanted
     * @return a List of Strings giving the paths to the files and directories 
     * on the class path
     */
    @NonNull
    protected List<String> getClasspath(@NonNull IJavaProject jproject) {
        return getClasspath(jproject,false);
    }
    
    /** Gets the classpath of the given project, interpreting all Eclipse entries
     * and converting them into file system paths to directories or jars.
     * @param jproject the Java project whose class path is wanted
     * @param onlyExported if true, only classpath entries that are marked as exported are added to the output list
     * @return a List of Strings giving the paths to the files and directories 
     * on the class path
     */
    @NonNull
    protected List<String> getClasspath(@NonNull IJavaProject jproject, boolean onlyExported) {
        try {
            IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
            IClasspathEntry[] entries = jproject.getResolvedClasspath(true);
            List<String> cpes = new LinkedList<String>();
            for (IClasspathEntry i: entries) {
                if (onlyExported && !i.isExported()) continue;
                //Log.log("ENTRY " +  i);
                switch (i.getEntryKind()) {
                    case IClasspathEntry.CPE_CONTAINER:
                    case IClasspathEntry.CPE_SOURCE:
                        IResource p = root.getFolder(i.getPath());
                        String s = p.getLocation().toString();
                        cpes.add(s);
                        break;
                    case IClasspathEntry.CPE_LIBRARY:
                        IFile f = root.getFile(i.getPath());
                        if (f == null || f.getLocation() == null) {
                            cpes.add(i.getPath().toString());
                        } else {
                            cpes.add(f.getLocation().toString());
                        }
                        break;
                    case IClasspathEntry.CPE_PROJECT:
                        // FIXME - this has not been tested - pay attention to isExported?
                        IProject proj = (IProject)root.getProject(i.getPath().toString());
                        List<String> plist = getClasspath(JavaCore.create(proj),true);
                        cpes.addAll(plist);
                        break;
                    case IClasspathEntry.CPE_VARIABLE:
                        // Variables and containers are already resolved
                    default:
                        Log.log("CPE NOT HANDLED" + i);  // FIXME - and better error message
                    break;
                }
            }
            Bundle b = Platform.getBundle("org.jmlspecs.OpenJMLUI");
            URL url = b.getEntry("");
            URI uri = url.toURI();
            String s = uri.getPath();
            //String ss = url.toExternalForm(); // FIXME - should this be used?
            cpes.add(s);
            return cpes;
        } catch (URISyntaxException e) {
            throw new Utils.OpenJMLException("Failed in determining classpath",e);
        } catch (JavaModelException e) {
            throw new Utils.OpenJMLException("Failed in determining classpath",e);
        }
    }

    /** This class is an implementation of the interfaces needed to provide input
     * to and launch editors in the workspace.
     * @author David R. Cok
     */
    public static class StringStorage implements IStorage, IStorageEditorInput {
        /** The initial content of the editor */
        private @NonNull String content;
        /** The name of storage unit (e.g. the file name) */
        private @NonNull String name;
        
        /** A constructor for a new storage unit */
        //@ assignable this.*;
        public StringStorage(@NonNull String content, @NonNull String name) { 
            this.content = content; 
            this.name = name; 
        }
        
        /** Interface method that returns the contents of the storage unit */
        @Override
        public InputStream getContents() throws CoreException {
            return new ByteArrayInputStream(content.getBytes());
        }

        /** Returns the path to the underlying resource
         * @return null (not needed for readonly Strings)
         */
        @Override
        public IPath getFullPath() {
            return null;
        }

        /** Returns the name of the storage object 
         * @return the name of the storage unit
         */
        @Override
        @Query
        public @NonNull String getName() { return name; }

        /** Returns whether the storage object is read only
         * @return always true
         */
        @Override
        public boolean isReadOnly() { return true; }

        /** Returns the object adapted to the given class.  It appears we can
         * ignore this and always return null.
         * @return null
         */
        @Override @SuppressWarnings("rawtypes") // Can't add type parameters because the parent interface does not have them
        public @Nullable Object getAdapter(@NonNull Class arg0) { return null; }

        /** Returns self
         * @return this object
         */
        //@ ensures \return == this;
        @Override
        public IStorage getStorage() throws CoreException {
            return (IStorage)this;
        }
        
        /** Returns whether the underlying storage object exists
         * @return always true
         */
        @Override
        public boolean exists() {
            return true;
        }
        
        /** Returns an ImageDescriptor, here ignored
         * @return always null
         */
        @Override
        public ImageDescriptor getImageDescriptor() {
            return null;
        }
        
        /** Returns a corresponding Persistable object, here ignored
         * @return always null
         */
        @Override
        public IPersistableElement getPersistable() {
            return null;
        }
        
        /** Return the text desired in a tool tip, here the name of the
         * storage unit
         */
        @NonNull
        @Override
        public String getToolTipText() {
            return name;
        }

    }

    /** Launches a read-only text editor with the given content and name
     * @param content the content of the editor
     * @param name the name (as in the title) of the editor
     */
    public void launchEditor(String content,String name) {
        try {
            IEditorInput editorInput = new StringStorage(content,name);
            IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
            IWorkbenchPage page = window.getActivePage();
            page.openEditor(editorInput, "org.eclipse.ui.DefaultTextEditor");
        } catch (Exception e) {
            showExceptionInUI(null,e);
        }
    }

    /** Launches a read-only text editor with the given content and name
     * @param content the content of the editor
     * @param name the name (as in the title) of the editor
     */
    public void launchJavaEditor(String content,String name) {
        try {
            IEditorInput editorInput = new StringStorage(content,name);
            IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
            IWorkbenchPage page = window.getActivePage();
            page.openEditor(editorInput, org.eclipse.jdt.ui.JavaUI.ID_CU_EDITOR);
        } catch (Exception e) {
            showExceptionInUI(null,e);
        }
    }

    /** Launches a editable Java editor with the given file
     * @param file the file to edit
     */
    public void launchJavaEditor(IFile file) {
        try {
            IFileEditorInput editorInput = new FileEditorInput(file);
            IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
            IWorkbenchPage page = window.getActivePage();
            page.openEditor(editorInput, org.eclipse.jdt.ui.JavaUI.ID_CU_EDITOR );
        } catch (Exception e) {
            showExceptionInUI(null,e);
        }
    }

    /** Deletes the markers in any of the objects in the List that are 
     * IResource objects; if the object is a container, markers are deleted for
     * any resources in the container; other kinds of objects are ignored.
     * @param <T> just the type of the list
     * @param list a list of objects whose markers are to be deleted
     * @param shell the current shell for dialogs (or null for default)
     */
    public <T> void deleteMarkers(List<T> list, @Nullable Shell shell) {
        int maxdialogs = 5;
        for (T t: list) {
            if (!(t instanceof IResource)) continue;
            IResource resource = (IResource)t;
            try {
                deleteMarkers(resource,shell);
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
    
    /** Deletes the markers (and highlighting) in the given resource; 
     * if the object is a container, markers are deleted for
     * any resources in the container; other kinds of objects are ignored.
     * @param resource the resource whose markers are to be deleted
     * @param shell the current shell for dialogs (or null for default)
     */
    public void deleteMarkers(IResource resource, @Nullable Shell shell) {
        try {
        	if (Activator.options.uiverbosity >= 2) Log.log("Deleting markers in " + resource.getName());
        	resource.deleteMarkers(JML_MARKER_ID, false, IResource.DEPTH_INFINITE);
        	resource.deleteMarkers(ESC_MARKER_ID, false, IResource.DEPTH_INFINITE);
        	resource.deleteMarkers(JML_HIGHLIGHT_ID, false, IResource.DEPTH_INFINITE);
        	resource.deleteMarkers(JML_HIGHLIGHT_ID + "True", false, IResource.DEPTH_INFINITE);
        	resource.deleteMarkers(JML_HIGHLIGHT_ID + "False", false, IResource.DEPTH_INFINITE);
        	resource.deleteMarkers(JML_HIGHLIGHT_ID + "Exception", false, IResource.DEPTH_INFINITE);
        } catch (CoreException e) {
        	String msg = "Failed to delete markers on " + resource.getProject();
        	Log.errorlog(msg, e);
        	Utils.showMessage(shell,"JML Plugin Exception",msg + " - " + e);
        }
    }
    
    // TODO _ needs more documentation
    
    public Map<IJavaProject, Set<IResource>> enabledMaps = new HashMap<IJavaProject, Set<IResource>>();

    public Set<IResource> getSet(IJavaProject jp) {
        Set<IResource> set = enabledMaps.get(jp);
        if (set == null) {
            enabledMaps.put(jp, set = new HashSet<IResource>());
        }
        return set;
    }

    public void markForRac(boolean enable, ISelection selection, IWorkbenchWindow window, @Nullable Shell shell) {
        List<IResource> res = getSelectedResources(selection,window,shell);
        final Map<IJavaProject,List<IResource>> sorted = sortByProject(res);
        for (final IJavaProject jp : sorted.keySet()) {
            final List<IResource> ores = sorted.get(jp);
            for (IResource r: ores) mark(enable,r, getSet(jp));
        }
    }
    
    protected void mark(boolean enable, IResource r, Set<IResource> set) {
        try {
            if (r instanceof IFolder) {
                for (IResource rr: ((IFolder)r).members()) {
                    mark(enable,rr,set);
                }
            } else if (r instanceof IFile) {
                if (r.getName().endsWith(".java")) {
                    if (enable) set.add(r);
                    else set.remove(r);
                }
            } else {
            	if (Activator.options.uiverbosity >= 2) Log.log("Not handling " + r.getClass());
            }
        } catch (CoreException e) {
            Log.errorlog("Core Exception while traversing Resource tree (mark for RAC)",e);
            // just continue
        }
    }
    
    public void highlight(final IResource r, final int finalOffset, final int finalEnd, final int type) {
		IWorkspaceRunnable runnable = new IWorkspaceRunnable() {
			public void run(IProgressMonitor monitor) throws CoreException {
				String name = type == IProverResult.Span.NORMAL ? ".JMLHighlight" : 
								type == IProverResult.Span.TRUE ? ".JMLHighlightTrue" : 
								type == IProverResult.Span.FALSE ? ".JMLHighlightFalse" :
								type == IProverResult.Span.EXCEPTION ? ".JMLHighlightException" :
									".JMLHighlight";
				IMarker marker = r.createMarker(Activator.PLUGIN_ID + name);
//				marker.setAttribute(IMarker.LINE_NUMBER, 
//									finalLineNumber >= 1? finalLineNumber : 1);
//				if (column >= 0) {
					marker.setAttribute(IMarker.CHAR_START, finalOffset); 
					marker.setAttribute(IMarker.CHAR_END, finalEnd);
//				}
				// Note - it appears that CHAR_START is measured from the beginning of the
				// file and overrides the line number when drawing the squiggly 
				// The line number is used in the information about the problem in
				// the Problem View

				//marker.setAttribute(IMarker.SEVERITY,b == null ? 0 : b ? 2 : 1);
				//marker.setAttribute(IMarker.MESSAGE, finalErrorMessage);
			}
		};
		try {
			r.getWorkspace().run(runnable, null);
		} catch (CoreException e) {
            Log.errorlog("Core Exception while highlighting",e);
            // just continue
		}

    }
    
    public void clearForRac(ISelection selection, IWorkbenchWindow window, final @Nullable Shell shell) {
        List<IResource> res = getSelectedResources(selection,window,shell);
        final Map<IJavaProject,List<IResource>> sorted = sortByProject(res);

        for (final IJavaProject jp : sorted.keySet()) {
            final List<IResource> ores = sorted.get(jp);
            Job j = new Job("JML Clear RAC") {
                public IStatus run(IProgressMonitor monitor) {
                    boolean c = false;
                    try {
                        IFolder dir = jp.getProject().getFolder(Activator.options.racbin);
                        for (IResource r: ores) clear(r,dir);
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

        for (final IJavaProject jp : sorted.keySet()) {
            final List<IResource> ores = sorted.get(jp);
            IFolder dir = jp.getProject().getFolder(Activator.options.racbin);
            for (IResource r: ores) clear(r,dir);
        }
    }
    
    protected void clear(IResource r, IFolder dir) {
        try {
            if (r instanceof IFolder) {
                for (IResource rr: ((IFolder)r).members()) {
                    clear(rr,dir);
                }
            } else if (r instanceof IFile) {
                if (r.getName().endsWith(".java")) {
                    ICompilationUnit cu = (ICompilationUnit)r.getAdapter(ICompilationUnit.class);
                    if (cu != null) {
                        for (IType t: cu.getTypes()) {
                            String s = t.getFullyQualifiedName();
                            s = s.replace('.','/');
                            s = s.substring(0,s.length()-(".java").length());
                            s = s + ".class";
                            IFile f = dir.getFile(s);
                            f.delete(IResource.FORCE,null);
                        }
                    }
                }
            } else {
            	if (Activator.options.uiverbosity >= 2) Log.log("Not handling " + r.getClass());
            }
        } catch (CoreException e) {
            Log.errorlog("Core Exception while traversing Resource tree (mark for RAC)",e);
            // just continue
        }
    }
 
    /**
     * Creates a map indexed by IJavaProject, with the value for
     * each IJavaProject being a Collection consisting of the subset
     * of the argument that belongs to the Java project.
     * 
     * @param elements The set of elements to sort
     * @return The resulting Map of IJavaProject to Collection
     */
    /*@ requires elements != null;
              requires elements.elementType <: IResource ||
                       elements.elementType <: IJavaElement;
              ensures \result != null;
     */
    public static @NonNull <T> Map<IJavaProject,List<T> > sortByProject(@NonNull Collection<T> elements) {
        Map<IJavaProject,List<T>> map = new HashMap<IJavaProject,List<T>>();
        Iterator<T> i = elements.iterator();
        while (i.hasNext()) {
            T o = i.next();
            IJavaProject jp;
            if (o instanceof IResource) {
                jp = JavaCore.create(((IResource)o).getProject());
            } else if (o instanceof IJavaElement) {
                jp = ((IJavaElement)o).getJavaProject();
            } else {
                Log.errorlog("INTERNAL ERROR: Unexpected content for a selection List - " + o.getClass(),null);
                continue;
            }
            if (jp != null && jp.exists()) addToMap(map,jp,o);
        }
        return map;
    }

    /**
     * If key is not a key in the map, it is added, with an empty
     * Collection for its value; then the given object is added
     * to the Collection for that key.
     * @param map A map of key values to Collections
     * @param key A key value to add to the map, if it is not
     *      already present
     * @param object An item to add to the Collection for the given key
     */
    private static <T> void addToMap(@NonNull Map<IJavaProject,List<T>> map, @NonNull IJavaProject key, @NonNull T object) {
        List<T> list = map.get(key);
        if (list == null) map.put(key, list = new LinkedList<T>());
        list.add(object);
    }

    /**
     * Displays a message in a dialog in the UI thread - this may
     * be called from other threads.
     * @param shell  The shell to use to display the dialog, or 
     *      a top-level shell if the parameter is null
     * @param title  The title of the dialog window
     * @param msg  The message to display in the dialog
     */
    public void showMessageInUI(@Nullable Shell shell, 
            @NonNull final String title, @NonNull final String msg) {
        final Shell fshell = shell;
        Display d = fshell == null ? Display.getDefault() : fshell.getDisplay();
        d.asyncExec(new Runnable() {
            public void run() {
                MessageDialog.openInformation(
                        fshell,
                        title,
                        msg);
            }
        });
    }
    
    // TODO _ document
    public void showExceptionInUI(@Nullable Shell shell, Exception e) {
        String s = e.getMessage();
        if (s == null || s.isEmpty()) s = e.getClass().toString();
        showMessageInUI(shell,"OpenJML Exception",s);
    }

    // FIXME - fix non-modal dialog
    /** 
     * Displays a message in a non-modal dialog in the UI thread - this may
     * be called from other threads.
     * @param shell  The shell to use to display the dialog, or 
     *      a top-level shell if the parameter is null
     * @param title  The title of the dialog window
     * @param msg  The message to display in the dialog
     */
    public void showMessageInUINM(@Nullable Shell shell, 
            @NonNull final String title, @NonNull final String msg) {
        final Shell fshell = shell;
        Display d = fshell == null ? Display.getDefault() : fshell.getDisplay();
        d.asyncExec(new Runnable() {
            public void run() {
                Dialog d = new NonModalDialog(
                        fshell,
                        title,
                        msg);
                d.open();
            }
        });
    }

    // FIXME this does not seem to be working
    static public class NonModalDialog extends MessageDialog {
        final static String[] buttons = { "OK" };
        public NonModalDialog(Shell shell, String title, String message) {
            super(new Shell(),title,null,message,INFORMATION,buttons,0);
            setShellStyle(getShellStyle()|SWT.MODELESS);
            setBlockOnOpen(false);
        }
    }
    
    public final static QualifiedName SPECSPATH_ID = new QualifiedName(Activator.PLUGIN_ID,"specspath");
    
    public List<IResource> getSpecsPath(IJavaProject jp) {
        try {
            String s = jp.getProject().getPersistentProperty(SPECSPATH_ID);
            //Log.log("RETRIEVED SPECSPATH: " + s);
            if (s == null) s = "";
            String[] names = s.split(",");
            List<IResource> files = new ArrayList<IResource>(names.length);
            for (String n: names) {
                if (n.length() > 0) {
                    Path p = new Path(n);
                    // We try a bunch of things, in order to do our best to read the
                    // format of what is stored.  Ideally it is the 
                    // toPortableString form of an IPath
                    IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
                    IResource f = root.findMember(p);
                    if (f == null) f = root.getFileForLocation(p);
                    if (f == null) f = root.getContainerForLocation(p);
                    p = new Path("C:"+n);
                    if (f == null) f = root.getFileForLocation(p);
                    if (f == null) f = root.getContainerForLocation(p);
                    if (f != null) {
                        //Log.log("  IFILE " + f + " " + f.getFullPath() + " " + f.getFullPath().toPortableString());
                        files.add(f);
                    } else {
                        Log.log("No such (open) location in the workspace (ignoring): " + n);
                    }
                }
            }
            return files;
        } catch (CoreException e) {
            Log.log("CoreException happened: " + e); // FIXME - error log?
            return new ArrayList<IResource>();
        }
    }

    static public void putSpecsPath(IJavaProject jp, List<IResource> files) {
        StringBuilder s = new StringBuilder();
        boolean isFirst = true;
        for (IResource n: files) {
            if (isFirst) isFirst = false; else s.append(",");
            s.append(n.getFullPath().toPortableString());
        }
        try {
            //Log.log("SAVED SPECSPATH: " + s.toString());
            jp.getProject().setPersistentProperty(SPECSPATH_ID,s.toString());
        } catch (CoreException e) {
            Log.log("CoreException happened: " + e); // FIXME - error log?
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
    static public void showMessage(Shell shell, String title, String msg) {
        MessageDialog.openInformation(
                shell,
                title,
                msg);
    }
    
    // FIXME -document

    /** Shows a dialog regarding an exception that has been thrown; this must be
     * called within the UI thread.
     */
    public void topLevelException(Shell shell, String title, Exception e) {
        //e.printStackTrace(sw); // TODO - show the stack trace?
        showMessage(shell,"JML Top-level Exception: " + title,
                e.toString());
    }

    static public final String[] suffixes = { ".refines-java", ".refines-spec", ".refines-jml", ".java", ".spec", ".jml" };

    /** This method returns an int giving the precedence of the suffix of the
     * file name: -1 indicates not a JML file; 0 is the preferred suffix;
     * increasing positive numbers indicate decreasing precedence of suffixes.
     * @param name the file name to be assessed
     * @return the precedence of the suffix (0 highest, more positive lower, -1 is not JML)
     */
    @Pure
    static public int suffixOK(/*@ non_null */ String name) {
        int i = 0;
        for (String s : suffixes) {
            if (name.endsWith(s)) return i;
            i++;
        }
        return -1;
    }
    
    /** Returns an absolute, local file-system path to the internal run-time
     * library (which holds definitions of annotations and some runtime utilities
     * for RAC), or null without an error message if the library could not be found.
     * @return the absolute path
     */
    public String findInternalRuntime() {
    	String file = null;
        try {
            Bundle selfBundle = Platform.getBundle(Activator.PLUGIN_ID);
            if (selfBundle == null) {
            	if (Activator.options.uiverbosity >= 2) Log.log("No self plugin");
            } else {
                URL url;
                url = FileLocator.toFileURL(selfBundle.getResource(""));
                if (url != null) {
                    File root = new File(url.toURI());
                    if (root.isDirectory()) {
                        File f = new File(root,"jmlruntime.jar");
                        if (f.exists()) {
                        	file = f.toString();
                            if (Activator.options.uiverbosity >= 2) Log.log("Internal runtime location: " + file);
                        } else {
                        	f = new File(root,"../jmlruntime.jar");
                            if (f.exists()) {
                                file = f.toString();
                                if (Activator.options.uiverbosity >= 2) Log.log("Internal runtime location: " + file);
                            }
                        }
                    }
                }
            }
        } catch (Exception e) {
            Log.errorlog("Failure finding internal runtime",e);
        }
        return file;
    }

}
