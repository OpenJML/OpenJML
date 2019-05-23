/*
 * This file is part of the OpenJML plugin project. 
 * Copyright (c) 2006-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.InputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
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
import java.util.concurrent.atomic.AtomicInteger;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import org.eclipse.core.internal.resources.ResourceException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceRuleFactory;
import org.eclipse.core.resources.IStorage;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.core.runtime.jobs.JobGroup;
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
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkingSet;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.annotation.Query;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.Main.Cmd;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.eclipse.PathItem.ProjectPath;
import org.jmlspecs.openjml.esc.MethodProverSMT.Counterexample;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;
import org.osgi.framework.Bundle;

import com.sun.tools.javac.tree.JCTree;

// FIXME - review UI Utils class

/**
 * This class holds utility values and methods to support the Eclipse plugin for
 * OpenJML.
 * 
 * @author David Cok
 * 
 */
public class Utils {

    /** This class is used to wrap arbitrary exceptions coming from OpenJML */
    public static class OpenJMLException extends RuntimeException {
        /** Default serial version ID */
        private static final long serialVersionUID = 1L;

        /**
         * Used to signal some unexpected error situation in doing JML
         * processing.
         */
        public OpenJMLException(@NonNull String error) {
            super(error);
        }

        /**
         * Used to signal some unexpected error situation in doing JML
         * processing.
         */
        public OpenJMLException(@NonNull String error, @NonNull Exception e) {
            super(error, e);
        }
    }

    /** An empty string */
    final public static @NonNull String emptyString = ""; //$NON-NLS-1$

    /** A single comma */
    final public static @NonNull String comma = ","; //$NON-NLS-1$

    /** An single space */
    final public static @NonNull String space = " "; //$NON-NLS-1$

    /** The .java suffix */
    final public static @NonNull String dotJava = ".java";  //$NON-NLS-1$

    /** The .jml suffix */
    final public static @NonNull String dotJML = ".jml";  //$NON-NLS-1$

    /**
     * A map relating java projects to the instance of OpenJMLInterface that
     * handles openjml stuff for that project. We have a separate instance for
     * each project since options can be different by project.
     */
    final protected @NonNull
    Map<IJavaProject, OpenJMLInterface> projectMap = new HashMap<IJavaProject, OpenJMLInterface>();

    /**
     * Returns the unique OpenJMLInterface for a given project
     * 
     * @param jproject
     *            the Java project whose interface is desired
     * @return the OpenJMLInterface for that project
     */
    public @NonNull
    OpenJMLInterface getInterface(@NonNull IJavaProject jproject) {
        OpenJMLInterface i = projectMap.get(jproject);
        if (i == null) {
            projectMap.put(jproject, i = new OpenJMLInterface(jproject));
        }
        return i;
    }

    protected String getInternalSystemSpecs() {
        String filesep = "/"; // Not File.separator I think //$NON-NLS-1$
        String specsDir = "specs";
        StringBuilder ss = new StringBuilder();
        try {
            boolean somethingPresent = false;
            //			String versionString = System.getProperty("java.version"); //$NON-NLS-1$
            //			int version = 7; // the current default
            //			if (versionString.startsWith("1.") && versionString.length() > 3 //$NON-NLS-1$
            //					&& (version = (versionString.charAt(2) - '0')) >= 4 && version <= 9) {
            //				// found OK version number
            //			} else {
            //				Log.log("Unrecognized version: " + versionString); //$NON-NLS-1$
            //				version = 7; // default, if the version string is in an
            //								// unexpected format
            //			}

            String[] defspecs = new String[8]; // null entries OK

            Bundle specsBundle = Platform.getBundle(Env.SPECS_PLUGIN_ID);
            if (specsBundle == null) {
                if (Options.uiverboseness)
                    Log.log("No specification plugin " + Env.SPECS_PLUGIN_ID); //$NON-NLS-1$
            } else {
                String loc = null;
                URL url = FileLocator.toFileURL(specsBundle.getResource(emptyString));
                File root = new File(url.toURI());
                loc = root.getAbsolutePath();
                loc = loc.replace("\\", "/");  //$NON-NLS-1$//$NON-NLS-2$
                if (Options.uiverboseness)
                    Log.log("JMLSpecs plugin found " + root + space //$NON-NLS-1$
                                            + root.exists());
                if (root.isFile()) {
                    // Presume it is a jar or zip file
                    JarFile j = new JarFile(root);
                    JarEntry f = j.getJarEntry(specsDir);
                    if (f != null)
                        defspecs[0] = loc + "!" + specsDir; //$NON-NLS-1$
                    j.close();
                } else if (root.isDirectory()) {
                    // Normal file system directory
                    File f = new File(root, specsDir); //$NON-NLS-1$
                    if (f.exists())
                        defspecs[0] = f.getAbsolutePath().replace(
                                                '\\', '/'); //$NON-NLS-1$
                } else {
                    if (Options.uiverboseness)
                        Log.log("Expected contents (specs subdirectory) not found in " + Env.SPECS_PLUGIN_ID + " bundle at "
                                                + root);
                }
                for (String z : defspecs) {
                    if (z != null) {
                        somethingPresent = true;
                        if (Options.uiverboseness)
                            Log.log("Set library specspath defaults from the Specs plugin");
                        break;
                    }
                }
            }
            if (!somethingPresent) {
                Bundle selfBundle = Platform.getBundle(Env.PLUGIN_ID);
                if (selfBundle == null) {
                    if (Options.uiverboseness)
                        Log.log("No self plugin"); //$NON-NLS-1$
                } else {
                    URL url = FileLocator.toFileURL(selfBundle.getResource(Strings.slash));
                    if (url != null) {
                        File root = new File(url.toURI());
                        if (Options.uiverboseness)
                            Log.log("Self bundle found " + root + Strings.space //$NON-NLS-1$
                                                    + root.exists());
                        int i = 0;
                        if (root.isDirectory()) {
                            File f = new File(root, ".." + filesep //$NON-NLS-1$
                                                    + specsDir);  //$NON-NLS-1$//$NON-NLS-2$
                            if (f.exists())
                                defspecs[i++] = f.toString();
                        } else {
                            JarFile j = new JarFile(root);
                            JarEntry f = j.getJarEntry(specsDir);
                            if (f != null)
                                defspecs[i++] = root + "!" + specsDir;
                            j.close();
                        }
                        if (i > 0)
                            somethingPresent = true;
                    }
                }
            }
            if (!somethingPresent)
                Log.errorlog("No internal library specs found", null);
            for (String z : defspecs)
                if (z != null) {
                    ss.append(z);
                    ss.append(File.pathSeparator);
                }
            if (ss.length() > 0)
                ss.setLength(ss.length() - File.pathSeparator.length()); // Remove the extraneous last path separator
        } catch (Exception e) {
            Log.log("Failure finding internal specs: " + e); //$NON-NLS-1$
        }
        return ss.toString();
    }

    /** Checks for dirty editors; pops up a dialog to ask the user what
     * to do; returns false if the operation is to be canceled.
     * @return
     */
    public boolean checkForDirtyEditors() {
        return PlatformUI.getWorkbench().saveAllEditors(true);
    }

    /**
     * This routine initiates (as a Job) checking the JML of all the Java files
     * in the selection; if any containers (including working sets) are
     * selected, the operation applies to the contents of the container ; if any
     * Java elements are selected (e.g. a method), the operation applies to the
     * containing file.
     * 
     * @param selection
     *            the current selection (ignored unless it is an
     *            IStructuredSelection)
     * @param window
     *            null or the currently active IWorkbenchWindow
     * @param shell
     *            the current shell
     */
    public void checkSelection(@Nullable final ISelection selection,
                            @Nullable final IWorkbenchWindow window, @NonNull final Shell shell) {
        if (!checkForDirtyEditors()) return;
        if (selection == null) {
            showMessage(shell, "JML Check", "Nothing selected to check");
            return;
        }
        List<IResource> res = getSelectedResources(selection, window, shell);
        if (res.size() == 0) {
            showMessage(shell, "JML Check", "Nothing appropriate to check");
            return;
        }
        deleteMarkers(res, shell);
        final Map<IJavaProject, List<IResource>> sorted = sortByProject(res);
        Job j = new Job("JML Manual Check") {
            public IStatus run(IProgressMonitor monitor) {
                monitor.beginTask("JML type-checking", sorted.size());
                boolean c = false;
                for (final IJavaProject jp : sorted.keySet()) { // FIXME - should impose an order on the projects
                    final List<IResource> ores = sorted.get(jp);
                    try {
                        getInterface(jp).executeExternalCommand(Cmd.CHECK,
                                                ores, monitor,false);
                    } catch (Exception e) {
                        showExceptionInUI(shell, null, e);
                        c = true;
                    }
                    monitor.worked(1);
                }
                return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
            }
        };
        //        IResourceRuleFactory ruleFactory = 
        //                ResourcesPlugin.getWorkspace().getRuleFactory();
        //// FIXME        ISchedulingRule rule = ruleFactory.markerRule(r);
        //		if (sorted.keySet().size() == 1) {
        //			j.setRule(sorted.keySet().iterator().next().getProject());
        //		} else {
        //			j.setRule(ResourcesPlugin.getWorkspace().getRoot());
        //		}
        j.setRule(null);
        j.setUser(true); // true since the job has been initiated by an end-user
        j.schedule();
    }

    /** Shows a message in a popup dialog with the given title */
    public void showMessage(final String title, String message) {

        Display.getDefault().asyncExec(new Runnable() {
            @Override
            public void run() {
                ErrorDialog.openError(Display.getDefault().getActiveShell(),
                                        title, message, null, IStatus.INFO);
            }
        });
    }

    public void inferSelection(ISelection selection, @Nullable IWorkbenchWindow window, @Nullable final Shell shell) {
        if (!checkForDirtyEditors())
            return;
        if (selection == null) {
            showMessage(shell, "Infer JML Contracts", "Nothing selected to infer");
            return;
        }
        final List<Object> res = getSelectedElements(selection, window, shell);
        if (res.size() == 0) {
            showMessage(shell, "Infer JML Contracts", "Nothing selected or applicable to infer");
            return;
        }
        final Map<IJavaProject, List<Object>> sorted = sortByProject(res);
        deleteMarkers(res, shell); 
        for (final IJavaProject jp : sorted.keySet()) {
            inferProject(jp, sorted.get(jp), shell, "Infer JML Contracts");
        }
    }

    /**
     * This routine initiates (as a Job) executing ESC on all the Java files in
     * the selection; if any containers are selected, the operation applies the
     * contents of the container (including working sets). If a Type or Method
     * is selected, the operation is applied to that element only. (FIXME - not
     * yet)
     * 
     * @param selection
     *            the current selection (ignored unless it is an
     *            IStructuredSelection)
     * @param window
     *            null or the currently active IWorkbenchWindow
     * @param shell
     *            the current shell
     */
    public void checkESCSelection(ISelection selection,
                            @Nullable IWorkbenchWindow window, @Nullable final Shell shell) {
        if (!checkForDirtyEditors()) return;
        if (selection == null) {
            showMessage(shell, "ESC", "Nothing selected to check");
            return;
        }
        final List<Object> res = getSelectedElements(selection, window, shell);
        if (res.size() == 0) {
            showMessage(shell, "ESC", "Nothing selected or applicable to check");
            return;
        }
        final Map<IJavaProject, List<Object>> sorted = sortByProject(res);
        for (IJavaProject jp: sorted.keySet()) JMLNature.autoJMLEnable(jp.getProject());
        deleteMarkers(res, shell); // FIXME - does this trigger a rebuild?
        JobControl.JobParameters jobParameters = JobControl.launchJobControlDialog(selection,window,shell);
        if (jobParameters == null) return;
        if (jobParameters.alwaysSave) jobParameters.save();

        for (final IJavaProject jp : sorted.keySet()) {
            checkESCProject(jp,sorted.get(jp),shell,"Static Checks - Manual",jobParameters);
        }
    }


    JobControl data = new JobControl();


    /** Creates and schedules a Job to do the desired computation.
     */
    public void checkESCProject(final IJavaProject jp, /*@ nullable */ final List<Object> ores, /*@ nullable */Shell shell, String reason, JobControl.JobParameters jobParameters) {
        try {
            JMLNature.autoJMLEnable(jp.getProject());
            OpenJMLInterface iface = getInterface(jp);
            JobControl.JobStrategy strategy1 = new JobControl.SelectedItemStrategy(jp,ores,2,reason);
            if (jobParameters != null) strategy1 = jobParameters.strategy.getConstructor(IJavaProject.class,List.class,int.class,String.class).newInstance(jp,ores,2,reason);
            final JobControl.JobStrategy strategy = strategy1;
            int qs = strategy.queues();
            int work = strategy.totalWork();

            Job job = new Job("Master ESC Job") {
                public IStatus run(IProgressMonitor m) {
                    SubMonitor parentSubMonitor = SubMonitor.convert(m);
                    parentSubMonitor.beginTask("Static checking project " + jp.getElementName(), work+1);
                    //parentSubMonitor = null;
                    final Job jjob = this;
                    if (qs == 1) {
                        while (true) {
                            Job j = strategy.nextJob(iface,0,parentSubMonitor);
                            iface.setMonitor(parentSubMonitor);
                            if (j == null) break;
                            j.setRule(null);
                            j.setUser(false); // false so we do not get progress monitors for sub-jobs
                            try { 
                                j.schedule();
                                // join will throw OperationCanceledException if the monitor is canceled
                                // Use a timeout here so we can frequently poll for cancelation requests
                                // Timeout amount is somewhat arbitrary
                                while (!j.join(500,parentSubMonitor)) {} // spin until finished or canceled 
                                // Check for cancelation request after the job completed
                                if (j.getResult() == Status.CANCEL_STATUS) {
                                    jjob.cancel(); // TODO - do we need this?
                                    Log.log("Cancelled without completing all proof tasks - A");
                                    return Status.CANCEL_STATUS;
                                }
                                Log.log.equals("Completed a job " + j.getResult());
                            } catch (InterruptedException e) { 
                                break; // TODO - What is the correct action here?
                            } catch (OperationCanceledException e) {
                                // Cancelation request during join()
                                j.cancel();
                                jjob.cancel(); // TODO - do we need this? or call done()
                                iface.api.abort();
                                Log.log("Cancelled without completing all proof tasks");
                                return Status.CANCEL_STATUS;
                            }
                        }
                        return Status.OK_STATUS;
                    } else {
                        JobGroup jobGroup = new JobGroup("",qs,qs);
                        Job[] jobs = new Job[qs];
                        OpenJMLInterface ifaces[] = new OpenJMLInterface[qs];
                        for (int i=0; i<ifaces.length; ++i) ifaces[i] = new OpenJMLInterface(jp);
                        AtomicInteger aq = new AtomicInteger();
                        while (true) {
                            while (aq.get()<qs) {
                                int q = 0;
                                for (;q < qs; q++) if (jobs[q] == null) break;
                                Job j = strategy.nextJob(ifaces[q],q,parentSubMonitor);
                                jobs[q] = j;
                                if (j == null) break;
                                aq.incrementAndGet();
                                j.addJobChangeListener(new JobChangeAdapter() { public void done(IJobChangeEvent e) {
                                    for (int i=0; i<qs; i++) if (e.getJob() == jobs[i]) { 
                                        jobs[i] = null; 
                                        break; 
                                    }
                                    int qq = aq.decrementAndGet();
                                    Log.log("Job completed " + qq);
                                    Job.getJobManager().wakeUp(jjob);
                                } });
                                j.setJobGroup(jobGroup);
                                j.setRule(null);
                                j.setUser(false); // false, to suppress the progress monitor dialog for subtasks
                                j.schedule();
                                Log.log.equals("Scheduled a job " + q + " " + aq.get());
                            }
                            if (aq.get() == qs) {
                                while (aq.get() == qs) {
                                    // Could have a race: if check test above; job completes; decrements aq; wakes this job; then this job sleeps 
                                    //Log.log("Going to sleep " + aq.get());
                                    jjob.sleep(); // sleep until some job terminates and calls wakeUp()
                                    //Log.log("Awake " + aq.get());
                                }
                            } else {
                                break;
                            }
                        }
                        Log.log("Going to join " + aq.get());
                        try { jobGroup.join(0,null); }  catch (InterruptedException e) {}
                        Log.log("All done " + aq.get());
                        return Status.OK_STATUS;
                    }
                };
            };
            IFile f = jp.getProject().getFile(".joblock");
            if (!f.exists()) {
                try {
                    f.create(new ByteArrayInputStream(new byte[0]), IResource.NONE, null);
                } catch (ResourceException e) {
                    // Already exists? - we get here despite the f.exists test.
                } catch (Exception e) {
                    Log.log("Failed to lock " + e.getMessage());
                }
            }
            job.setRule(f);
            //job.belongsTo(job);
            job.setUser(true);  // true to show the composite progress monitor
            job.schedule();
            //			job.join();
            //			if (job.getResult() == Status.CANCEL_STATUS) {
            //			    Log.log("Job queue canceled");
            //			}
        } catch (Exception e) {
            // FIXME Failure
        }
    }


    public void inferProject(final IJavaProject jp, final List<?> ores, /*@ nullable */Shell shell, String reason) {

        Job j = Job.create(reason, monitor -> {
            monitor.beginTask("Inferring specification of " + jp.getElementName(), 1);
            boolean c = false;
            try {
                if (ores == null) {
                    LinkedList<Object> list = new LinkedList<Object>();
                    list.add(jp);
                    final List<Object> res = list;
                    getInterface(jp).executeInferCommand(Cmd.INFER, res,
                                            monitor);
                } else if (ores.size() != 0){
                    getInterface(jp).executeInferCommand(Cmd.INFER, ores,
                                            monitor);
                }
            } catch (Exception e) {
                // FIXME - this will block, preventing progress on the rest of the projects
                Log.errorlog("Exception during Inference - " + jp.getElementName(), e);
                showExceptionInUI(null, "Exception during Inference - " + jp.getElementName(), e);
                c = true;
            }

            // no return value needed when using an ICoreRunnable (since Neon)
        });



        IResourceRuleFactory ruleFactory = 
                                ResourcesPlugin.getWorkspace().getRuleFactory();
        j.setRule(jp.getProject());
        j.setUser(true); // true since the job has been initiated by an end-user
        j.schedule();
    }


    static public java.util.Properties getProperties() {
        return org.jmlspecs.openjml.Utils.findProperties(null);
    }

    static public java.util.Properties readProperties() {
        // FIXME - as different projects are processed, they continually
        // overwrite each other's properties
        // Log.log("About to read properties");
        java.util.Properties properties = new java.util.Properties();
        {
            // Note: It appears that a file in the workspace root is not seen as
            // a member of the workspace - just projects - because findMember on
            // the workspace root returns null. So we find the file directly in
            // the local file system.
            IPath path = ResourcesPlugin.getWorkspace().getRoot().getLocation()
                                    .append(org.jmlspecs.openjml.Strings.propertiesFileName);
            try {
                boolean found = org.jmlspecs.openjml.Utils.readProps(
                                        properties, path.toFile().getAbsolutePath());
                if (found && Options.uiverboseness)
                    Log.log("Properties read from the workspace: "
                                            + path.toOSString());
            } catch (java.io.IOException e) {
                Log.errorlog("Failed to read a properties file", e);
            }
        }
        return properties;
    }

    public java.util.Properties readProjectProperties(IProject project) {
        // FIXME - as different projects are processed, they continually
        // overwrite each other's properties
        // Log.log("About to read properties");
        readProperties();
        java.util.Properties properties = new java.util.Properties();
        {
            // Log.log("Project location: " + project.getLocation());
            IResource res = project
                                    .findMember(org.jmlspecs.openjml.Strings.propertiesFileName);
            if (res != null) {
                try {
                    boolean found = org.jmlspecs.openjml.Utils.readProps(
                                            properties, res.getLocation().toOSString());
                    if (found && Options.uiverboseness)
                        Log.log("Properties read from the project directory: "
                                                + res.getLocation().toOSString());
                } catch (java.io.IOException e) {
                    Log.errorlog("Failed to read a properties file", e);
                }
            }
        }
        return properties;
    }

    /**
     * This routine initiates (as a Job) compiling RAC for all the Java files in
     * the selection; if any containers are selected, the operation applies the
     * contents of the container (including working sets); if any Java elements
     * are selected (e.g. a method), the operation applies to the containing
     * file.
     * 
     * @param selection
     *            the current selection (ignored unless it is an
     *            IStructuredSelection)
     * @param window
     *            null or the currently active IWorkbenchWindow
     * @param shell
     *            the current shell
     */
    public void racSelection(final @NonNull ISelection selection,
                            @Nullable final IWorkbenchWindow window, final Shell shell) {
        if (!checkForDirtyEditors()) return;

        // For now at least, only IResources are accepted for selection
        final @NonNull List<IResource> res = getSelectedResources(selection, window, shell);
        if (res.size() == 0) {
            showMessage(shell, "JML RAC Selected", "Nothing appropriate to check");
            return;
        }


        final @NonNull Map<IJavaProject, List<IResource>> sorted = sortByProject(res);
        for (final IJavaProject jp : sorted.keySet()) {
            checkForJmlEnabled(shell,jp);
            Job j = new Job("Compiling Runtime Assertions on selected resources") {
                public IStatus run(IProgressMonitor monitor) {
                    boolean c = false;
                    try {
                        getInterface(jp).executeExternalCommand(Cmd.RAC,
                                                sorted.get(jp), monitor,false);
                    } catch (Exception e) {
                        showExceptionInUI(shell,
                                                "Failure while compiling runtime assertions", e);
                        c = true;
                    }
                    return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
                }
            };
            IResourceRuleFactory ruleFactory = 
                                    ResourcesPlugin.getWorkspace().getRuleFactory();
            // FIXME        ISchedulingRule rule = ruleFactory.markerRule(r);
            j.setRule(jp.getProject());
            j.setUser(true); // true since the job has been initiated by an
            // end-user
            j.schedule();
        }
    }

    public void checkForJmlEnabled(Shell shell, IJavaProject project) {
        try {
            if (JMLNature.isJMLNature(project.getProject())) return;
        } catch (CoreException e) {
            // Log an error but proceed
            Log.errorlog("Core Exception encountered on trying to check for a JML nature on project " + project.getElementName() + ": ",e);
        }
        List<String> cpes = getClasspath(project);
        for (String s: cpes) {
            if (s.contains("jmlruntime")) return;
        }

        String msg = "You are compiling classes with RAC in a project that is not" +
                                " enabled for JML. The compiled executable will require the JML" +
                                " runtime library on its path to run successfully. You can either\n" +
                                "\n" +
                                "1) Enable JML for the project by selecting the project and then the menu action 'Enable JML'. " +
                                "This will add the internal instance of jmlruntime.jar to the project classpath.\n" +
                                "\n    or   \n\n" +
                                "2) You can manually add an instance of jmlruntime.jar as an 'External Jar' in the Project Properties/Java Build Path/Libraries dialog." +
                                " An instance of jmlruntime.jar is available, for example, in the download of the OpenJML command-line tools." +
                                "\n\nShall I Enable JML on the " + project.getElementName() + " project for you now?";
        boolean ok = showConfirmInUI(shell,"OpenJML classpath warning",msg);
        if (ok) {
            JMLNature.enableJMLNature(project.getProject());
        }
    }

    /**
     * This routine initiates (as a Job) compiling RAC for all the Java files in
     * the selection; if any containers are selected, the operation applies the
     * contents of the container (including working sets); if any Java elements
     * are selected (e.g. a method), the operation applies to the containing
     * file.
     * 
     * @param selection
     *            the current selection (ignored unless it is an
     *            IStructuredSelection)
     * @param window
     *            null or the currently active IWorkbenchWindow
     * @param shell
     *            the current shell
     */
    public void racMarked(final @NonNull ISelection selection,
                            @Nullable final IWorkbenchWindow window, final Shell shell) {

        if (!checkForDirtyEditors()) return;

        // For now at least, only IResources are accepted for selection
        final @NonNull Collection<IJavaProject> projects = getSelectedProjects(true,selection, window, shell);
        if (projects.size() == 0) {
            showMessage(shell, "JML RAC Marked", "No projects selected");
            return;
        }

        for (final IJavaProject jp : projects) {
            checkForJmlEnabled(shell,jp);
            racMarked(jp);
        }
    }

    public void racMarked(final IJavaProject jp) {
        Job j = new Job("Compiling Runtime Assertions on marked resources") {
            public IStatus run(IProgressMonitor monitor) {
                boolean c = false;
                try {
                    Set<IResource> resources = getRacFiles(jp);
                    getInterface(jp).executeExternalCommand(Cmd.RAC,
                                            resources, monitor,false);
                } catch (Exception e) {
                    showExceptionInUI(null,
                                            "Failure while compiling runtime assertions", e);
                    c = true;
                }
                return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
            }
        };
        IResourceRuleFactory ruleFactory = 
                                ResourcesPlugin.getWorkspace().getRuleFactory();
        // FIXME        ISchedulingRule rule = ruleFactory.markerRule(r);
        j.setRule(jp.getProject());
        j.setUser(true); // true since the job has been initiated by an
        // end-user
        j.schedule();
    }

    // TODO - document doBuildRac - put in a Job - or not - because called from
    // a computation thread anyway
    protected void doBuildRac(IJavaProject jproject,
                            List<IResource> resourcesToBuild, IProgressMonitor monitor) {
        Set<IResource> enabledForRac = getRacFiles(jproject);
        List<IResource> newlist = new ArrayList<IResource>(enabledForRac.size());
        for (IResource r : resourcesToBuild) {
            if (enabledForRac.contains(r))
                newlist.add(r);
        }
        if (newlist.size() != 0) {
            try {
                if (Options.uiverboseness)
                    Log.log("Starting RAC " + newlist.size() + " files");
                getInterface(jproject).executeExternalCommand(Cmd.RAC, newlist,
                                        monitor,false);
                if (Options.uiverboseness)
                    Log.log("Completed RAC");
            } catch (Exception e) {
                showExceptionInUI(null, null, e);
            }
        } else {
            if (Options.uiverboseness)
                Log.log("Nothing to RAC");
        }
    }

    /**
     * This routine initiates (as a Job) generating jmldoc pages for each
     * project in the selection. If non-projects are selected, the containing
     * project is used. For each project, the contents of the source folders are
     * documented.
     * 
     * @param selection
     *            the current selection (ignored unless it is an
     *            IStructuredSelection)
     * @param window
     *            null or the currently active IWorkbenchWindow
     * @param shell
     *            the current shell
     */
    public void jmldocSelection(final ISelection selection,
                            @Nullable final IWorkbenchWindow window, final Shell shell) {
        // For now at least, only IResources are accepted for selection
        final List<IResource> res = getSelectedResources(selection, window,
                                shell);
        if (res.size() == 0) {
            showMessage(shell, "JML - jmldoc", "Nothing appropriate to check");
            return;
        }
        Job j = new Job("Generating jmldoc") {
            public IStatus run(IProgressMonitor monitor) {
                boolean c = false;
                try {
                    Collection<IJavaProject> projects = getSelectedProjects(
                                            false, selection, window, shell);
                    if (projects.size() == 0)
                        projects = getSelectedProjects(true, selection, window,
                                                shell);
                    for (IJavaProject p : projects) {
                        getInterface(p).generateJmldoc(p);
                    }
                } catch (Exception e) {
                    showExceptionInUI(shell, null, e);
                    c = true;
                }
                return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
            }
        };
        // FIXME - use some proper scheduling rule?
        j.setRule(ResourcesPlugin.getWorkspace().getRoot());
        j.setUser(true);
        j.schedule();
    }

    /**
     * This method pops up an information window to show the specifications of
     * each selected type, method, or field. Executed entirely in the UI thread.
     * 
     * @param selection
     *            the selection (multiple items may be selected)
     * @param window
     *            the current window
     * @param shell
     *            the current shell
     */
    public void showSpecsForSelection(ISelection selection,
                            @Nullable IWorkbenchWindow window, Shell shell) {
        List<Object> list = getSelectedElements(selection, window, shell);
        if (list.isEmpty()) {
            showMessage(shell, "OpenJML - Show specifications for Java element",
                                    "Choose a type, method or field whose specifications are to be shown");
            return;
        }
        String sn = emptyString;
        for (Object o : list) {
            try {
                String s = null;
                if (o instanceof IType) {
                    IType t = (IType) o;
                    s = getInterface(t.getJavaProject()).getAllSpecs(t);
                    if (s != null)
                        s = s.replace('\r', ' ');
                    sn = "type " + t.getFullyQualifiedName();
                } else if (o instanceof IMethod) {
                    IMethod m = (IMethod) o;
                    s = getInterface(m.getJavaProject()).getAllSpecs(m);
                    if (s != null)
                        s = s.replace('\r', ' ');
                    sn = "method "
                                            + m.getDeclaringType().getFullyQualifiedName()
                                            + "." + m.getElementName();
                } else if (o instanceof IField) {
                    IField f = (IField) o;
                    s = getInterface(f.getJavaProject()).getSpecs(f);
                    if (s != null)
                        s = s.replace('\r', ' ');
                    sn = "field "
                                            + f.getDeclaringType().getFullyQualifiedName()
                                            + "." + f.getElementName();
                } else if (o instanceof ICompilationUnit) {
                    ICompilationUnit cu = (ICompilationUnit)o;
                    IType[] types = cu.getTypes();
                    StringBuilder ss = new StringBuilder();
                    for (IType t: types) {
                        s = getInterface(t.getJavaProject()).getAllSpecs(t);
                        if (s != null) s = s.replace('\r', ' ');
                        if (s.length() == 0)
                            s = "<no specifications>";
                        ss.append(s);
                        ss.append("\n");
                    }
                    sn = "classes in file " + cu.getPath().toString();
                    s = ss.toString();
                } else if (o instanceof IFile) {
                    IFile f = (IFile) o;
                    ICompilationUnit cu = JavaCore.createCompilationUnitFrom(f);
                    IType[] types = cu.getTypes();
                    StringBuilder ss = new StringBuilder();
                    for (IType t: types) {
                        s = getInterface(t.getJavaProject()).getAllSpecs(t);
                        if (s != null) s = s.replace('\r', ' ');
                        if (s.length() == 0)
                            s = "<no specifications>";
                        ss.append(s);
                        ss.append("\n");
                    }
                    sn = "classes in file " + f.toString();
                    s = ss.toString();
                } else {
                    showMessageInUINM(shell, "Specifications",
                                            "Cannot show specifications for a " + o.getClass());
                    return;
                }
                if (s != null) {
                    if (s.length() == 0)
                        s = "<no specifications>";
                    showMessageInUINM(shell, "Specifications for " + sn, s);
                } else if (sn != null) {
                    showMessageInUINM(shell, "Specifications",
                                            "No JML check has been run");
                    return;
                }
            } catch (Exception e) {
                showMessage(shell, "OpenJML - Exception", e.getMessage());
            }
        }
    }

    public List<IType> findMatchingClassNames(IJavaProject jp, String text) throws JavaModelException {
        String classname = Strings.slash + text.replace('.', '/') + ".class"; //$NON-NLS-1$ 
        String dotText = Strings.dot + text;
        String dollarText = Strings.dollar + text;
        List<IType> matches = new LinkedList<IType>();
        for (IClasspathEntry cpe : jp.getResolvedClasspath(true)) {
            // cpe is SOURCE, PROJECT, or LIBRARY
            if (cpe.getEntryKind() == IClasspathEntry.CPE_LIBRARY) {
                // findPackageFragmentRoots does not work for
                // library entries
                try {
                    ZipFile z = new ZipFile(cpe.getPath()
                                            .toString());
                    Enumeration<? extends ZipEntry> en = z
                                            .entries();
                    while (en.hasMoreElements()) {
                        ZipEntry ze = en.nextElement();
                        String zs = ze.getName();
                        if (zs.endsWith(classname)) {
                            zs = zs.replace('/', '.');
                            zs = zs.substring(0, zs.length()
                                                    - ".class".length()); //$NON-NLS-1$
                            matches.add(jp.findType(zs,
                                                    (IProgressMonitor) null));
                        }
                    }
                    z.close();
                } catch (java.io.IOException ex) {
                    Log.errorlog("Failed to open jar file "
                                            + cpe.getPath().toString(), ex);
                    // Pretend there is no match
                }
            } else {
                for (IPackageFragmentRoot pfr : jp
                                        .findPackageFragmentRoots(cpe)) {
                    if (!pfr.isOpen())
                        continue;
                    for (IJavaElement element : pfr.getChildren()) { 
                        // element is a IPackageFragment
                        for (IJavaElement je : ((IPackageFragment) element)
                                                .getChildren()) { // je is aICompilationUnit
                            if (je instanceof ICompilationUnit) {
                                for (IType ee : ((ICompilationUnit) je).getAllTypes()) {
                                    if (ee.getFullyQualifiedName().endsWith(dotText)) {
                                        matches.add(ee);
                                    } else {
                                        matchNestedTypes(ee,dollarText,matches);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return matches;
    }

    protected void matchNestedTypes(IType ee, String dotText, List<IType> matches) throws JavaModelException {
        for (IJavaElement e: ee.getChildren()) {
            if (e instanceof IType) {
                IType t = (IType)e;
                if (t.getFullyQualifiedName().endsWith(dotText)) {
                    matches.add(t);
                } else {
                    matchNestedTypes(t,dotText,matches);
                }
            }
        }
    }

    /**
     * This method opens an editor on the specs corresponding to a selected
     * class; if text is selected, an attempt is made to interpret the text as
     * the name (possibly fully qualified) of a class; otherwise if a type is
     * selected that type is used; if a file or compilation unit is selected,
     * the primary type of that unit is used. Then we search for the
     * specifications file corresponding to that type. Executed entirely in the
     * UI thread.
     * 
     * @param selection
     *            the selection (multiple items may be selected)
     * @param window
     *            the current window
     * @param shell
     *            the current shell
     */
    public void openSpecEditorForSelection(ISelection selection,
                            @Nullable IWorkbenchWindow window, Shell shell) {
        // Note that we could get the specs file through IAPI. However, that
        // requires that the project be type-checked. Here we duplicate the
        // logic for looking up specification files, which is not good, but
        // there is less dependence on what is already typechecked, which is
        // good.
        ITextSelection textSelection = getSelectedText(selection);
        List<Object> list = new LinkedList<Object>();
        String text;
        if (textSelection != null && window != null
                                && (text = textSelection.getText()).length() != 0) {
            // We have some selected text - try to interpret it as a class name
            if (Options.uiverboseness)
                Log.log("Selected text: " + text); //$NON-NLS-1$
            // Get the string of text, with .class at the end
            String classname = "/" + text.replace('.', '/') + ".class"; //$NON-NLS-1$ //$NON-NLS-2$
            // Get the Java project corresponding to the file the text is in
            IEditorPart p = window.getActivePage().getActiveEditor();
            IEditorInput e = p == null ? null : p.getEditorInput();
            IFile o = e == null ? null : (IFile) e.getAdapter(IFile.class);
            IJavaProject jp = o == null ? null : JavaCore.create(o)
                                    .getJavaProject();
            List<IType> matches = new LinkedList<IType>();

            if (jp == null) {
                showMessageInUI(shell,
                                        Messages.OpenJMLUI_OpenSpecsEditor_DialogTitle,
                                        "Could not determine the containing Java project");
                return;
            }
            try {
                // FIXME - check that nested and secondary types work and
                // resolve eventually to the primary type
                // First try fully-qualified names
                IType t = jp.findType(text, (IProgressMonitor) null);
                if (t != null) {
                    matches.add(t);
                } else {
                    // Look for partial matches in the classpath of the project
                    matches = findMatchingClassNames(jp,text);
                }
            } catch (JavaModelException ex) {
                Log.errorlog(
                                        "Failed to match text to a type name because of an exception",
                                        ex);
                // Pretend there is no match
            }
            if (matches.size() == 1) {
                list.add(matches.get(0));
            } else if (matches.size() > 1) {
                StringBuilder sb = new StringBuilder();
                sb.append("More than one match of type names to ");
                sb.append(text);
                sb.append(" with no complete match. Specify the text more completely:");
                for (IType t : matches) {
                    sb.append(space);
                    sb.append(t.getFullyQualifiedName());
                }
                showMessageInUI(shell,
                                        Messages.OpenJMLUI_OpenSpecsEditor_DialogTitle,
                                        sb.toString());
                return;
            } else {
                showMessageInUI(shell,
                                        Messages.OpenJMLUI_OpenSpecsEditor_DialogTitle,
                                        "Could not find a type that matches \"" + text + "\"");
                return;
            }
        } else {
            list = getSelectedElements(selection, window, shell);
            if (list.isEmpty()) {
                showMessageInUI(shell,
                                        Messages.OpenJMLUI_OpenSpecsEditor_DialogTitle,
                                        "Nothing selected to open editors for");
                return;
            }
        }
        String kinds = emptyString;
        IResource firstEditableLocation = null;
        // FIXME - perhaps put the Dialog boxes outside the loop and accumulate all the information
        outer: for (Object o : list) {
            try {
                IType t = null;
                IType origType = null;
                if (o instanceof IType) {
                    t = (IType) o;
                    origType = t;
                    t = t.getCompilationUnit().findPrimaryType();
                } else if (o instanceof ICompilationUnit) {
                    t = ((ICompilationUnit) o).findPrimaryType();
                } else if (o instanceof IFile) {
                    ICompilationUnit cu = JavaCore.createCompilationUnitFrom((IFile) o);
                    t = cu.findPrimaryType();
                } else if (o instanceof IAdaptable) {
                    ICompilationUnit cu = (ICompilationUnit) ((IAdaptable) o)
                                            .getAdapter(ICompilationUnit.class);
                    if (cu != null)
                        t = cu.findPrimaryType();
                    if (t == null)
                        t = (IType) ((IAdaptable) o).getAdapter(IType.class);
                }
                if (t == null) {
                    kinds = kinds + o.getClass() + space;
                    continue;
                }
                if (origType == null) origType = t;
                String name = t.getFullyQualifiedName().replace('.', '/');
                String pname = t.getPackageFragment().getElementName();
                if (pname.isEmpty()) {
                    showMessageInUI(shell, "OpenJML", "It does not appear that the target file is in a source folder, so I can't search for a specifications file.");
                    return;
                }
                pname = pname.replace('.', '/');
                String[] fullnames = new String[suffixes.length];
                for (int i = 0; i < suffixes.length; i++)
                    fullnames[i] = name + suffixes[i];
                String[] absolutePaths = PathItem.getAbsolutePath(
                                        t.getJavaProject(), Utils.SPECSPATH_ID).split(
                                                                File.pathSeparator);
                List<File> roots = new LinkedList<File>();
                for (String p : absolutePaths) {
                    File f = new File(p);
                    if (f.exists())
                        roots.add(f);
                    else {
                        // FIXME - warn?
                    }
                }
                for (String fname : fullnames) {
                    for (File root : roots) {
                        if (root.isDirectory()) {
                            if (firstEditableLocation == null) {
                                firstEditableLocation = ResourcesPlugin
                                                        .getWorkspace()
                                                        .getRoot()
                                                        .getFileForLocation(
                                                                                new Path(root.getAbsolutePath()));
                            }
                            File ff = new File(root, fname);
                            if (!ff.exists())
                                continue;
                            IResource r = ResourcesPlugin
                                                    .getWorkspace()
                                                    .getRoot()
                                                    .getFileForLocation(
                                                                            new Path(ff.getAbsolutePath()));
                            if (r == null) {
                                showMessageInUI(
                                                        shell,
                                                        Messages.OpenJMLUI_OpenSpecsEditor_DialogTitle,
                                                        "The specifications for type "
                                                                                + origType.getFullyQualifiedName()
                                                                                + " are in "
                                                                                + Env.eol
                                                                                + ff.getAbsolutePath()
                                                                                + Env.eol
                                                                                + "but an editor can not be opened since the location is not in the workspace."
                                                                                + Env.eol
                                                                                + "Try linking to the package root from within the project.");
                                continue outer;
                            }
                            if (r.exists() && r instanceof IFile) {
                                launchJavaEditor((IFile) r);
                                showMessageInUI(
                                                        shell,
                                                        Messages.OpenJMLUI_OpenSpecsEditor_DialogTitle,
                                                        "The specifications for type "
                                                                                + origType.getFullyQualifiedName()
                                                                                + " are in " + Env.eol 
                                                                                + r.getLocation().toString());
                                return;
                            }
                        } else {
                            ZipFile jarfile = new ZipFile(root);
                            ZipEntry jarentry = jarfile.getEntry(fname);
                            if (jarentry != null) {
                                // FIXME - this will launch duplicate editors
                                InputStream is = jarfile
                                                        .getInputStream(jarentry);
                                int size = (int) jarentry.getSize();
                                byte[] bytes = new byte[size];
                                is.read(bytes, 0, size);
                                String s = new String(bytes);
                                showMessage(
                                                        shell,
                                                        Messages.OpenJMLUI_OpenSpecsEditor_DialogTitle,
                                                        "Specification file for "
                                                                                + t.getFullyQualifiedName()
                                                                                + " in " + Env.eol
                                                                                + jarfile.getName() + Env.eol
                                                                                + " is read-only");
                                String nm = jarentry.getName();
                                int k = nm.lastIndexOf('/');
                                if (k >= 0)
                                    nm = nm.substring(k + 1);
                                launchJavaEditor(s, nm);
                                return;
                            }
                            jarfile.close();
                        }
                    }
                }
                showMessage(
                                        shell,
                                        Messages.OpenJMLUI_OpenSpecsEditor_DialogTitle,
                                        kinds.length() == 0 ? "Nothing found for which to open an editor"
                                                                : "Cannot show specification files for "
                                                                + kinds);
            } catch (Exception e) {
                showExceptionInUI(shell,
                                        "Failure while finding specifications file", e);
                return;
            }
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
            printClass(w, t, imports);
        } catch (JavaModelException e) {
            w.println("<Error in generating default content>");
        }
        w.close();
        ww.println("package " + t.getPackageFragment().getElementName() + Strings.semicolon); //$NON-NLS-1$
        for (String s : imports) {
            ww.println("import " + s + Strings.semicolon); //$NON-NLS-1$
        }
        ww.println();
        ww.println(sw.toString());
        ww.close();
    }

    // FIXME - document
    protected void printClass(PrintWriter w, IType t, Set<String> imports)
                            throws JavaModelException {
        ITypeHierarchy th = t.newSupertypeHierarchy(null);
        IType sup = th.getSuperclass(t);
        if (sup.getFullyQualifiedName().equals("java.lang.Object")) //$NON-NLS-1$
            sup = null;
        IType[] ifaces = th.getSuperInterfaces(t);
        if (sup != null)
            imports.add(sup.getPackageFragment().getElementName());
        for (IType i : ifaces)
            imports.add(i.getPackageFragment().getElementName());
        w.println();
        // FIXME - annotations
        w.print(Flags.toString(t.getFlags()));
        w.print(" class "); //$NON-NLS-1$
        printType(w, t, imports);
        if (sup != null) {
            w.print(" extends "); //$NON-NLS-1$
            printType(w, sup, imports);
        }
        if (ifaces.length > 0)
            w.print(" implements"); //$NON-NLS-1$
        boolean isFirst = true;
        for (IType i : ifaces) {
            if (isFirst)
                isFirst = false;
            else
                w.print(Strings.comma);
            w.print(Strings.space);
            printType(w, i, imports);
        }
        w.println(" {");
        w.println();
        // w.println("  //@ requires true;");
        // w.println("  //@ ensures true;");
        // w.println("  //@ static_initalizer;");
        // w.println();
        // w.println("  //@ requires true;");
        // w.println("  //@ ensures true;");
        // w.println("  //@ initalizer;");
        //
        // for (IMethod m : t.getMethods()) {
        // w.println();
        // w.print("    ");
        // // FIXME - annotations
        // w.print(Flags.toString(m.getFlags()));
        // w.print(" ");
        // w.print(m.getReturnType());
        // w.print(" ");
        // w.print(m.getElementName());
        // w.print("(");
        // boolean isFirst2 = true;
        // String[] pn = m.getParameterNames();
        // String[] pt = m.getParameterTypes();
        // for (int i=0; i<pn.length; i++) {
        // if (isFirst2) isFirst2 = false; else w.print(", ");
        // // FIXME _ modifierse
        // w.print(pt[i]);
        // w.print(" ");
        // w.print(pn[i]);
        // }
        // w.print(")");
        // // FIXME - exceptions
        // w.print(";");
        // }
        w.println();
        w.println("}"); //$NON-NLS-1$
    }

    // FIXME - document
    protected void printType(PrintWriter w, IType t, Set<String> imports)
                            throws JavaModelException {
        w.print(t.getElementName());
        ITypeParameter[] tparams = t.getTypeParameters();
        if (tparams.length != 0) {
            w.print("<"); //$NON-NLS-1$
            boolean isFirst = true;
            for (ITypeParameter tp : tparams) {
                if (isFirst)
                    isFirst = false;
                else
                    w.print(Strings.comma);
                w.print(tp.getElementName());
                String[] bounds = tp.getBounds();
                if (bounds.length > 0) {
                    w.print(" extends"); //$NON-NLS-1$
                    boolean isFirst2 = true;
                    for (String s : bounds) {
                        if (isFirst2)
                            isFirst2 = false;
                        else
                            w.print(" &"); //$NON-NLS-1$
                        w.print(Strings.space);
                        w.print(s);
                    }
                }
            }
            w.print(">"); //$NON-NLS-1$
        }
    }

    /**
     * This method pops up an information window to show the proof result for
     * each selected method. Executed entirely in the UI thread.
     * 
     * @param selection
     *            the selection (multiple items may be selected)
     * @param window
     *            the current window
     * @param shell
     *            the current shell
     */
    public void showProofInfoForSelection(ISelection selection,
                            @Nullable IWorkbenchWindow window, Shell shell, boolean showDetails) {
        List<Object> olist = getSelectedElements(selection, window, shell);
        List<IMethod> list = new LinkedList<IMethod>();
        for (Object o : olist) {
            if (o instanceof IMethod)
                list.add((IMethod) o);
            // Ignore anything that does not match. Other types of items can be
            // selected, particularly with a MenuAction.
        }
        if (list.isEmpty()) {
            showMessage(shell, "JML", //$NON-NLS-1$
                                    "No methods were selected for the 'show proof info' operation");
        } else {
            for (IMethod m : list) {
                OpenJMLInterface jml = getInterface(m.getJavaProject());
                jml.showProofInfo(m, shell, showDetails);
            }
        }
    }

    /**
     * This method pops up an information window to show the value of an
     * expression in the current counterexample. Uses the computational thread.
     * 
     * @param selection
     *            the selection (multiple items may be selected)
     * @param window
     *            the current window
     * @param shell
     *            the current shell
     */
    public void showCEValueForTextSelection(ISelection selection,
                            @Nullable IWorkbenchWindow window, Shell shell) {
        if (!checkForDirtyEditors()) return;
        ITextSelection selectedText = getSelectedText(selection);
        if (selectedText == null) {
            showMessage(shell, "JML", "No text is selected");
            return;
        }
        int pos = selectedText.getOffset();
        int end = pos + selectedText.getLength() - 1;
        String s = selectedText.getText();
        IResource r = getSelectedResources(selection, window, shell).get(0);
        // FIXME - need to do this in another thread. ?
        String result = getInterface(JavaCore.create(r.getProject()))
                                .getCEValue(pos, end, s, r);
        showMessage(shell, "Counterexample value", result);
    }

    /**
     * This method interprets the selection returning a List of IResources or
     * IJavaElements, and ignoring things it does not know how to handle. The
     * selection is ignored if it is not an IStructuredSelection (e.g.
     * ITextSelections are ignored). If the selection is empty or the resulting
     * list is empty, and 'window' is non-null, then the routine attempts to
     * find a resource that corresponds to the currently active editor.
     * <UL>
     * <LI>IJavaElement - returned in the list
     * <LI>IResource - added directly to list, whether a file or a container
     * <LI>working set - adds the elements of the working set if they can be
     * converted (through IAdaptor) to an IResource
     * <LI>otherwise - attempts to be converted to an IResource, and added to
     * list if successful, ignored otherwise
     * </UL>
     * 
     * @param selection
     *            The selection to inspect
     * @param window
     *            The window in which a selected editor exists, or null
     * @param shell
     *            the shell to use in displaying information dialogs, or null to
     *            use a default shell
     * @return A List of IResource or IJavaElement
     */
    public List<Object> getSelectedElements(@NonNull ISelection selection,
                            @NonNull IWorkbenchWindow window, @Nullable Shell shell) {
        List<Object> list = new LinkedList<Object>();
        if (!selection.isEmpty() && selection instanceof IStructuredSelection) {
            IStructuredSelection structuredSelection = (IStructuredSelection) selection;
            for (Iterator<?> iter = structuredSelection.iterator(); iter
                                    .hasNext();) {
                Object element = iter.next();
                if (element instanceof IJavaElement) {
                    list.add(element);
                } else if (element instanceof IResource) {
                    // Log.log("Selected " + ((IResource)element).getName());
                    list.add(element);
                } else if (element instanceof IWorkingSet) {
                    for (IAdaptable a : ((IWorkingSet) element).getElements()) {
                        IResource r = (IResource) a.getAdapter(IResource.class);
                        if (r != null)
                            list.add(r);
                    }
                    continue;
                } else if (element instanceof IAdaptable) {
                    // TODO: curious as to just what might fall into this
                    // category
                    IResource r = ((IResource) ((IAdaptable) element)
                                            .getAdapter(IResource.class));
                    if (r != null)
                        list.add(r);
                }
            }
        } else {
            // We had nothing selected
            // Look for the active editor instead
            try {
                IEditorPart p = window.getActivePage().getActiveEditor();
                IEditorInput e = p == null ? null : p.getEditorInput();
                Object o = e == null ? null : e.getAdapter(ICompilationUnit.class);
                o = o != null ? o : e != null ? e.getAdapter(IFile.class) : null;
                o = o == null ? e : o;
                if (o != null) {
                    // Log.log("Selected " + o);
                    list.add(o);
                }
            } catch (Exception ee) {
                Log.errorlog("Exception when finding selected targets: " + ee,
                                        ee);
                showMessage(window.getShell(), "JML Plugin Exception",
                                        "Exception occurred when finding selected targets: "
                                                                + ee);
            }
        }
        return list;
    }

    // TODO - document
    public ITextSelection getSelectedText(@NonNull ISelection selection) {
        if (selection instanceof ITextSelection) {
            return (ITextSelection) selection;
        } else {
            return null;
        }
    }

    /**
     * This method interprets the selection returning a List of IResources or
     * IJavaElements, and ignoring things it does not know how to handle. The
     * selection is ignored if it is not an IStructuredSelection (e.g.
     * ITextSelections are ignored). If the selection is empty or the resulting
     * list is empty, and 'window' is non-null, then the routine attempts to
     * find a resource that corresponds to the currently active editor.
     * <UL>
     * <LI>IJavaElement - adds the containing java project
     * <LI>IResource - adds the containing project, as a Java project, if it is
     * one
     * <LI>working set - adds the elements of the working set if they are Java
     * projects
     * <LI>otherwise - attempts to be converted to a IJavaProject or an
     * IResource, and added to list if successful, ignored otherwise
     * </UL>
     * 
     * @param convert
     *            if false, then returned elements were precisely Java Projects
     *            in the selection; if true, the returned projects may also be
     *            the containing projects of selected non-project elements
     * @param selection
     *            The selection to inspect
     * @param window
     *            The window in which a selected editor exists, or null
     * @param shell
     *            the shell to use in displaying information dialogs, or null to
     *            use a default shell
     * @return A List of IResource or IJavaElement
     */
    public Collection<IJavaProject> getSelectedProjects(boolean convert,
                            @NonNull ISelection selection, @NonNull IWorkbenchWindow window,
                            @Nullable Shell shell) {
        Set<IJavaProject> list = new HashSet<IJavaProject>();
        if (!selection.isEmpty()) {
            if (selection instanceof IStructuredSelection) {
                IStructuredSelection structuredSelection = (IStructuredSelection) selection;
                for (Iterator<?> iter = structuredSelection.iterator(); iter
                                        .hasNext();) {
                    Object element = iter.next();
                    if (!convert) {
                        if (element instanceof IJavaProject)
                            list.add((IJavaProject) element);
                    } else if (element instanceof IJavaElement) {
                        list.add(((IJavaElement) element).getJavaProject());
                    } else if (element instanceof IResource) {
                        IJavaProject jp = JavaCore.create(((IResource) element)
                                                .getProject());
                        if (jp != null)
                            list.add(jp);
                    } else if (element instanceof IWorkingSet) {
                        for (IAdaptable a : ((IWorkingSet) element)
                                                .getElements()) {
                            // IJavaProject jp =
                            // JavaCore.create(((IResource)element).getProject());
                            IJavaProject jp = (IJavaProject) a
                                                    .getAdapter(IJavaProject.class);
                            if (jp != null)
                                list.add(jp);
                        }
                        continue;
                    } else if (element instanceof IAdaptable) {
                        // TODO: curious as to just what might fall into this
                        // category
                        IJavaProject jp = (IJavaProject) ((IAdaptable) element)
                                                .getAdapter(IJavaProject.class);
                        if (jp != null)
                            list.add(jp);
                        else {
                            IResource r = ((IResource) ((IAdaptable) element)
                                                    .getAdapter(IResource.class));
                            jp = JavaCore.create(((IResource) element)
                                                    .getProject());
                            if (r != null)
                                list.add(jp);
                        }
                    }
                }
                // } else {
                // showMessage(shell,"Unknown selection",selection.getClass().toString());
            }
        }
        if (convert && list.size() == 0) {
            // We had nothing selected or it was not a structured selection
            // Look for the active editor instead
            try {
                IEditorPart p = window.getActivePage().getActiveEditor();
                IEditorInput e = p == null ? null : p.getEditorInput();
                IFile o = e == null ? null : (IFile) e.getAdapter(IFile.class);
                if (o != null) {
                    IJavaProject jp = JavaCore.create(o.getProject());
                    if (jp != null)
                        list.add(jp);
                }
            } catch (Exception ee) {
                Log.errorlog("Exception when finding selected targets: " + ee,
                                        ee);
                showMessage(window.getShell(), Messages.OpenJMLUI_ExceptionTitle,
                                        "Exception occurred when finding selected targets: "
                                                                + ee);
            }
        }
        return list;
    }

    /**
     * This method interprets the selection returning a List of IResources, and
     * ignoring things it does not know how to handle; note that the resources
     * in the returned list are not necessarily Java files. The selection is
     * ignored if it is not an IStructuredSelection (e.g. ITextSelections are
     * ignored). If the selection is empty and 'window' is non-null, then the
     * routine attempts to find a resource that corresponds to the currently
     * active editor.
     * <UL>
     * <LI>IResource - added directly to list, whether a file or a container
     * <LI>working set - adds the elements of the working set if they can be
     * converted (through IAdaptor) to an IResource
     * <LI>IJavaElement - adds the IResource that contains the element
     * <LI>otherwise - ignored
     * </UL>
     * 
     * @param selection
     *            The selection to inspect
     * @param window
     *            The window in which a selected editor exists
     * @param shell
     *            the shell to use in displaying information dialogs
     * @return A List of IResources found in the selection
     */
    public List<IResource> getSelectedResources(@NonNull ISelection selection,
                            @Nullable IWorkbenchWindow window, @Nullable Shell shell) {
        List<IResource> list = new LinkedList<IResource>();
        if (selection instanceof IStructuredSelection && !selection.isEmpty() ) {
            IStructuredSelection structuredSelection = (IStructuredSelection) selection;
            for (Iterator<?> iter = structuredSelection.iterator(); iter
                                    .hasNext();) {
                Object element = iter.next();
                if (element instanceof IResource) {
                    list.add((IResource) element);
                } else if (element instanceof IWorkingSet) {
                    for (IAdaptable a : ((IWorkingSet) element).getElements()) {
                        IResource r = (IResource) a.getAdapter(IResource.class);
                        if (r != null)
                            list.add(r);
                    }
                    continue;
                } else if (element instanceof IJavaElement) {
                    // try {
                    IResource r = ((IJavaElement) element).getResource();
                    if (r != null)
                        list.add(r);
                    else if (element instanceof IAdaptable
                                            && (r = (IResource) ((IAdaptable) element)
                                            .getAdapter(IResource.class)) != null) {
                        list.add(r);
                    } else {
                        if (Options.uiverboseness)
                            Log.log("No resource for "
                                                    + ((IJavaElement) element).getElementName());
                    }
                }
            }
        } else {
            // We had nothing selected
            // Look for the active editor instead
            try {
                IEditorPart p = window.getActivePage().getActiveEditor();
                IEditorInput e = p == null ? null : p.getEditorInput();
                IResource o = e == null ? null : (IFile) e
                                        .getAdapter(IFile.class);
                if (o != null) {
                    // Log.log("Selected " + o);
                    list.add(o); // This is an IFile
                }
            } catch (Exception ee) {
                Log.errorlog("Exception when finding selected targets: " + ee,
                                        ee);
                showMessage(shell, "JML Plugin Exception",
                                        "Exception occurred when finding selected targets: "
                                                                + ee);
            }
        }
        return list;
    }

    /**
     * Alters whether the JML nature is enabled or disabled for the given
     * selected objects. The operation makes sense only for IJavaProject
     * objects; if other types of objects are selected, the enclosing
     * IJavaProject is used; if there is none, the selected object is ignored.
     * The operation is performed entirely in the UI thread (and should be
     * called from the UI thread).
     * 
     * @param enable
     *            if true, the JML nature is enabled; if false, it is disabled
     * @param selection
     *            the objects selected in the UI
     * @param window
     *            the current window
     * @param shell
     *            the current shell (for any dialogs)
     */
    public void changeJmlNatureSelection(boolean enable, ISelection selection,
                            IWorkbenchWindow window, Shell shell) {
        Collection<IJavaProject> list = Activator.utils()
                                .getSelectedProjects(true, selection, window, shell);
        Iterator<IJavaProject> i = list.iterator();
        if (!i.hasNext()) {
            Utils.showMessage(shell, "JML Plugin", "No Java projects selected");
            return;
        }
        int maxdialogs = 5;
        while (i.hasNext()) {
            IJavaProject p = i.next();
            try {
                if (enable)
                    JMLNature.enableJMLNature(p.getProject());
                else
                    JMLNature.disableJMLNature(p.getProject());
                PlatformUI.getWorkbench().getDecoratorManager()
                .update(Env.JML_DECORATOR_ID);
            } catch (Exception e) {
                if (window != null && (maxdialogs--) > 0) {
                    Utils.showMessage(
                                            shell,
                                            "JML Plugin Exception",
                                            "Exception while "
                                                                    + (enable ? "enabling" : "disabling")
                                                                    + " JML "
                                                                    + (p != null ? "on " + p.getElementName()
                                                                    : "") + e.toString());
                }
                Log.errorlog(
                                        "Failed to "
                                                                + (enable ? "enable" : "disable")
                                                                + " JML nature"
                                                                + (p != null ? " on project "
                                                                                        + p.getElementName() : ""), e);
            }
        }
        if (Options.uiverboseness)
            Log.log("Completed JML Nature operation ");
    }

    // Do this right here in the UI thread
    // FIXME - should resource things be happening in another thread?
    /**
     * Deletes all JML markers from the items selected, right within the UI
     * thread, without a progress dialog. The resources for which markers are
     * deleted are those returned by Utils.getSelectedResources. This should be
     * called from the UI thread.
     * 
     * @param selection
     *            the IStructuredSelection whose markers are to be deleted
     * @param window
     *            the current workbench window, or null (used in
     *            getSelectedResources)
     * @param shell
     *            the current Shell, or null for the default shell (for message
     *            dialogs)
     */
    public void deleteMarkersInSelection(ISelection selection,
                            IWorkbenchWindow window, Shell shell) {
        if (selection == null) {
            showMessage(shell, "JML Plugin",
                                    "Nothing selected to delete markers of");
            return;
        }
        List<IResource> list = getSelectedResources(selection, window, shell);
        if (list.isEmpty()) {
            showMessage(shell, "JML Plugin",
                                    "Nothing appropriate to delete markers of");
            return;
        }
        deleteMarkers(list, shell);
        return;
    }

    public @Nullable PathItem toPathItem(IJavaProject jp, Object r) {
        IResource f;
        if (r instanceof IPackageFragmentRoot) {
            IPackageFragmentRoot pfr = (IPackageFragmentRoot) r;
            f = pfr.getResource();
        } else if (r instanceof IFile
                                && "jar".equals(((IFile) r).getFileExtension())) {
            f = (IFile) r;
        } else if (!(r instanceof IFolder)) {
            return null;
        } else {
            f = (IFolder) r;
        }
        PathItem p;
        if (f.getProject().equals(jp.getProject())) {
            // Same project - use a project relative path
            p = new PathItem.ProjectPath(f.getProjectRelativePath()
                                    .toString());
        } else {
            p = new PathItem.WorkspacePath(f.getFullPath().toString());
        }
        return p;
    }

    // FIXME - add/remove - a source folder that is in the ALL_SOURCE_FOLDERs
    // is not recognized as already present

    /**
     * Expects the selection to hold exactly one Java project, plus one or more
     * folders or jar files; those folders and jar files are added to the
     * beginning of the specs path for the given project.
     * 
     * @param selection the current selection in the UI
     * @param window    the currently active window
     * @param shell     the current shell (for dialogs)
     */
    public void addSelectionToSpecsPath(ISelection selection,
                            IWorkbenchWindow window, @Nullable Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(false,
                                selection, window, shell);
        if (projects.size() != 1) {
            showMessage(shell, "OpenJML - Add to Specs Path",
                                    "Select exactly one Java Project along with the desired folders");
            return;
        }
        IJavaProject jp = projects.iterator().next();
        List<Object> list = getSelectedElements(selection, window, shell);
        String notadded = emptyString;
        boolean added = false;
        for (Object r : list) {
            if (r instanceof IJavaProject || r instanceof IProject) continue;
            PathItem p = toPathItem(jp,r);
            if (p == null) {
                if (r instanceof IResource) notadded = notadded + ((IResource) r).getName() + space;
                continue;
            }
            try {
                if (PathItem.add(jp, Env.specsKey, p)) {
                    added = true;
                } else {
                    notadded = notadded + space + p.display();
                }
            } catch (CoreException e) {
                showMessage(shell, "OpenJML - Remove from Specs Path",
                                        "Exception on reading or writing persistent property: "
                                                                + e);
            }
        }
        if (notadded.length() != 0) {
            showMessage(shell, "JML - Add to Specs Path",
                                    "These were already present and not added:" + notadded);
        } else if (!added) {
            showMessage(shell, "JML - Add to Specs Path", "Nothing was added");
        }
    }

    /**
     * Expects the selection to hold exactly one Java project, plus one or more
     * folders or jar files; those folders and jar files are removed from the
     * the specs path of the given project.
     * 
     * @param selection
     *            the current selection in the UI
     * @param window
     *            the currently active window
     * @param shell
     *            the current shell (for dialogs)
     */
    public void removeSelectionFromSpecsPath(ISelection selection,
                            @Nullable IWorkbenchWindow window, @Nullable Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(false,
                                selection, window, shell);
        if (projects.size() != 1) {
            showMessage(shell, "JML - Remove from Specs Path",
                                    "Select exactly one Java Project along with the desired folders");
            return;
        }
        IJavaProject jp = projects.iterator().next();
        List<Object> list = getSelectedElements(selection, window, shell);
        String notremoved = emptyString;
        for (Object r : list) {
            IResource f;
            String n;
            if (r instanceof IJavaProject || r instanceof IProject) continue;
            PathItem p = toPathItem(jp,r);
            try {
                if (p == null) {
                    notremoved = notremoved + r + space;
                } else if (!PathItem.remove(jp, Env.specsKey, p)) {
                    notremoved = notremoved + p.display() + space;
                }
            } catch (CoreException e) {
                showMessage(shell, "OpenJML - Remove from Specs Path",
                                        "Exception on reading or writing persistent property: "
                                                                + e);
            }
        }
        if (notremoved.length() != 0) {
            showMessage(shell, "OpenJML - Remove from Specs Path",
                                    "These were not found: " + notremoved);
        }
    }

    /** Puts up dialogs to edit each the paths of each selected Java project. */
    public void manipulateSpecsPath(ISelection selection,
                            IWorkbenchWindow window, Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(true,
                                selection, window, shell);
        if (projects.isEmpty()) {
            showMessageInUI(shell,"OpenJML Paths Editor",
                                    "No projects selected");
            return;
        }
        final Shell finalShell = shell;
        for (IJavaProject jproject : projects) {
            final IJavaProject jp = jproject;
            // FIXME - none of these implementations lets the dialogs come up
            // simultaneously
            // Even if we inherit PathsEditor from ModelessDialog

            // Display d = finalShell == null ? Display.getDefault() :
            // finalShell.getDisplay();
            // d.asyncExec(new Runnable() {
            // public void run() {
            // Dialog dialog = new PathsEditor(finalShell,
            // "OpenJML Paths Editor - " + jp.getElementName(), jp);
            // dialog.create();
            // dialog.open(); // OK actions are handled in the dialog
            // }
            // });

            try {
                jproject.getProject().getWorkspace()
                .run(new IWorkspaceRunnable() {
                    public void run(IProgressMonitor monitor) {
                        Dialog dialog = new PathsEditor(finalShell,
                                                "OpenJML Paths Editor - "
                                                                        + jp.getElementName(), jp);
                        dialog.create();
                        dialog.open(); // OK actions are handled in the
                        // dialog
                    }
                }, null);
            } catch (CoreException e) {
                showExceptionInUI(shell, "Failure while editing paths", e);
            }

            // Dialog dialog = new PathsEditor(finalShell,
            // "OpenJML Paths Editor - " + jp.getElementName(), jp);
            // dialog.create();
            // dialog.open(); // OK actions are handled in the dialog

        }
    }

    /**
     * Shows the classpath for selected projects. SHould be called from the UI
     * thread; is executed entirely in the calling thread.
     * 
     * @param selection
     *            the current selection in the UI
     * @param window
     *            the currently active window
     * @param shell
     *            the currently active shell (or null for default)
     */
    public void showPaths(ISelection selection, IWorkbenchWindow window,
                            Shell shell) {
        Collection<IJavaProject> projects = getSelectedProjects(true,
                                selection, window, shell);
        if (projects.isEmpty()) {
            showMessage(shell, "Show JML Paths", "No projects selected");
        }
        for (IJavaProject jp : projects) {
            List<String> list = getClasspath(jp);
            StringBuilder ss = new StringBuilder();
            ss.append("Classpath:");
            ss.append(Env.eol);
            for (String s : list) {
                ss.append(s);
                ss.append(Env.eol);
            }
            ss.append(Env.eol);
            // source path
            ss.append("Source path:");
            ss.append(Env.eol);
            String sp = PathItem.getAbsolutePath(jp, Env.sourceKey);
            sp = sp.replace(File.pathSeparator, Env.eol);
            ss.append(sp);
            ss.append(Env.eol);
            ss.append(Env.eol);
            // specs path
            ss.append("Specs path:");
            ss.append(Env.eol);
            sp = PathItem.getAbsolutePath(jp, Env.specsKey);
            sp = sp.replace(File.pathSeparator, Env.eol);
            ss.append(sp);
            ss.append(Env.eol);

            showMessage(shell, "JML paths for project " + jp.getElementName(),
                                    "Edit the paths in the JML preferences or use the"
                                                            + Env.eol
                                                            + "Add to/Remove from JML Specs Path menu items"
                                                            + Env.eol + Env.eol + ss.toString());
        }
    }

    private boolean changingClasspath = false;

    /**
     * Adds a Library classpath entry holding the internal run-time library to
     * the end of the given project's classpath, if the library is not already
     * on the classpath. This will trigger a build, if auto-building is turned
     * on.
     * 
     * @param jproject
     *            the project whose classpath is to be adjusted
     */
    public IClasspathEntry addRuntimeToProjectClasspath(final IJavaProject jproject) {
        if (changingClasspath)
            return null;
        try {
            IClasspathEntry[] entries = jproject.getRawClasspath();
            for (IClasspathEntry i : entries) {
                if (i.getPath().lastSegment().equals(ClasspathVariableInitializer.OPENJML_RUNTIME_LIBRARY)) {
                    showMessageInUI(null,"OpenJML","Internal runtime library is already on the classpath");
                    return i;
                }
                if (i.getPath().lastSegment().equals(RUNTIME_LIBRARY)) {
                    showMessageInUI(null,"OpenJML","Classpath already contains a manually added jmlruntime.jar library");
                    return i;
                }
            }

            IClasspathEntry libentry = makeRuntimeLibEntry();

            final IClasspathEntry[] newentries = new IClasspathEntry[entries.length + 1];
            System.arraycopy(entries, 0, newentries, 0, entries.length);
            newentries[entries.length] = libentry;
            try {
                changingClasspath = true;
                if (Options.uiverboseness)
                    Log.log("Internal runtime being added to classpath: "
                                            + libentry);

                try {
                    jproject.getProject().getWorkspace()
                    .run(new IWorkspaceRunnable() {
                        public void run(IProgressMonitor monitor) {
                            try {
                                jproject.setRawClasspath(newentries,
                                                        monitor);
                            } catch (Exception e) {
                                showMessageInUI(null, "Error Dialog",
                                                        "Exception while changing classpath: "
                                                                                + e);
                            }
                        }
                    }, null);
                } catch (CoreException e) {
                    Log.errorlog("Core Exception while changing classpath", e);
                    // just continue
                }
            } finally {
                changingClasspath = false;
            }
            return libentry;
        } catch (JavaModelException e) {
            throw new Utils.OpenJMLException(
                                    "Failed in adding internal runtime library to classpath: "
                                                            + e.getMessage(), e);
        }
    }

    protected void removeFromClasspath(final IJavaProject jproject, IClasspathEntry entry) {
        if (changingClasspath)
            return;
        try {
            IClasspathEntry[] entries = jproject.getRawClasspath();
            final IClasspathEntry[] newentries = new IClasspathEntry[entries.length];
            int j = 0;
            if (entry == null) {
                for (IClasspathEntry i : entries) {
                    if (!i.getPath().lastSegment().equals(RUNTIME_LIBRARY) &&
                                            !i.getPath().lastSegment().equals(ClasspathVariableInitializer.OPENJML_RUNTIME_LIBRARY)) {
                        newentries[j++] = i;
                    }
                }
            } else {
                for (IClasspathEntry i : entries) {
                    if (!i.equals(entry)) {
                        newentries[j++] = i;
                    }
                }
            }
            if (j < entries.length) {
                final IClasspathEntry[] newerentries = new IClasspathEntry[j];
                System.arraycopy(newentries, 0, newerentries, 0, j);
                try {
                    changingClasspath = true;
                    if (Options.uiverboseness)
                        Log.log("Internal runtime being removed from classpath: "
                                                + entry);

                    try {
                        jproject.getProject().getWorkspace()
                        .run(new IWorkspaceRunnable() {
                            public void run(IProgressMonitor monitor) {
                                try {
                                    jproject.setRawClasspath(newerentries,
                                                            monitor);
                                } catch (Exception e) {
                                    showMessageInUI(null, "Error Dialog",
                                                            "Exception while changing classpath: "
                                                                                    + e);
                                }
                            }
                        }, null);
                    } catch (CoreException e) {
                        Log.errorlog("Core Exception while changing classpath", e);
                        // just continue
                    }
                } finally {
                    changingClasspath = false;
                }
            }
            return ;
        } catch (JavaModelException e) {
            throw new Utils.OpenJMLException(
                                    "Failed in removing internal runtime library from classpath: "
                                                            + e.getMessage(), e);
        }
    }

    /**
     * Gets the classpath of the given project, interpreting all Eclipse entries
     * and converting them into file system paths to directories or jars.
     * 
     * @param jproject
     *            the Java project whose class path is wanted
     * @return a List of Strings giving the paths to the files and directories
     *         on the class path
     */
    @NonNull
    protected List<String> getClasspath(@NonNull IJavaProject jproject) {
        return getClasspath(jproject, false);
    }

    /**
     * Gets the classpath of the given project, interpreting all Eclipse entries
     * and converting them into file system paths to directories or jars.
     * 
     * @param jproject
     *            the Java project whose class path is wanted
     * @param onlyExported
     *            if true, only classpath entries that are marked as exported
     *            are added to the output list
     * @return a List of Strings giving the paths to the files and directories
     *         on the class path
     */
    @NonNull
    protected List<String> getClasspath(@NonNull IJavaProject jproject,
                            boolean onlyExported) {
        try {
            IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
            IClasspathEntry[] entries = jproject.getResolvedClasspath(true);
            List<String> cpes = new LinkedList<String>();
            for (IClasspathEntry i : entries) {
                if (onlyExported && !i.isExported())
                    continue;
                // Log.log("ENTRY " + i);
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
                    // FIXME - this has not been tested - pay attention to
                    // isExported?
                    IProject proj = (IProject) root.getProject(i.getPath()
                                            .toString());
                    List<String> plist = getClasspath(JavaCore.create(proj),
                                            true);
                    cpes.addAll(plist);
                    break;
                case IClasspathEntry.CPE_VARIABLE:
                    // Variables and containers are already resolved
                default:
                    Log.errorlog(
                                            "An unexpected kind of ClassPathEntry was ignored (project "
                                                                    + jproject.getElementName() + "): " + i,
                                                                    null);
                    break;
                }
            }
            // Bundle b = Platform.getBundle("org.jmlspecs.OpenJMLUI");
            // URL url = b.getEntry("");
            // URI uri = url.toURI();
            // String s = uri.getPath();
            // String ss = url.toExternalForm(); // FIXME - should this be used?
            // We are trying to include the contents of OpenJMLUI on the
            // classpath
            // Why? Don't we already have annotations, specs, and the runtime
            // library? FIXME
            // This just ends up as a /
            // cpes.add(s);
            return cpes;
            // } catch (URISyntaxException e) {
            // throw new
            // Utils.OpenJMLException("Failed in determining classpath",e);
        } catch (JavaModelException e) {
            throw new Utils.OpenJMLException("Failed in determining classpath",
                                    e);
        }
    }

    public void refreshView() {
        Display d = Display.getDefault();
        d.asyncExec(new Runnable() {
            public void run() {
                try {
                    IViewPart view = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView(OpenJMLView.ID);
                    ((OpenJMLView)view).refresh();
                    ((OpenJMLView)view).start();
                } catch (PartInitException e) {
                    // FIXME - report error?
                }
            }
        });
    }

    public void refreshView(IJavaProject jproject, final String symname) {
        Display d = Display.getDefault();
        d.asyncExec(new Runnable() {
            public void run() {
                try {
                    IViewPart view = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView(OpenJMLView.ID);
                    ((OpenJMLView)view).refresh(jproject,symname);
                } catch (PartInitException e) {
                    // FIXME - report error?
                } catch (RuntimeException e) {
                    // FIXME - report error?
                }
            }
        });
    }

    /** Returns the ProofView, if it exists, null otherwise */
    static public OpenJMLView findView() {
        IWorkbench wb = PlatformUI.getWorkbench();
        IWorkbenchWindow w = wb.getActiveWorkbenchWindow();
        if (w != null) {
            IWorkbenchPage ap = w.getActivePage();
            IViewPart view = ap.findView(OpenJMLView.ID);
            return ((OpenJMLView)view);
        }

        for (IWorkbenchWindow ww: wb.getWorkbenchWindows()) {
            for (IWorkbenchPage pg: ww.getPages()) {
                IViewPart view = pg.findView(OpenJMLView.ID);
                return ((OpenJMLView)view);
            }
        }
        return null;
    }

    /** Creates (if needed) and returns the Proof View */
    static public OpenJMLView showView() {
        try {
            IWorkbench w = PlatformUI.getWorkbench();
            IWorkbenchWindow ww = w.getActiveWorkbenchWindow();
            IWorkbenchPage wp = ww.getActivePage();
            IViewPart view = wp.showView(OpenJMLView.ID);
            return ((OpenJMLView)view);
        } catch (PartInitException e) {
            // FIXME - report error?
            return null;
        }
    }

    /** Creates (if needed) and returns the trace view, setting the given data */
    public void setTraceView(final String methodName, final String text) {
        Display d = Display.getDefault();
        d.asyncExec(new Runnable() {
            public void run() {
                setTraceViewUI(null, methodName,text,true);
            }
        });
    }

    /** Creates (if needed) and returns the trace view, setting the given data; MUST be called from the UI thread */
    public void setTraceViewUI(/*@ nullable*/ TraceView tview, final String methodName, final String text, boolean show) {
        try {
            if (tview == null) {
                IViewPart view;
                if (show) {
                    view = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView(TraceView.ID);
                } else {
                    view = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().findView(TraceView.ID);
                }
                if (!(view instanceof TraceView)) return; // FIXME - this would be an internal error
                tview = (TraceView)view;
            }
            tview.setText(methodName, text);
        } catch (PartInitException e) {
            // FIXME - report error?
        }
    }

    public String currentTraceViewUISignature(/*@ nullable*/ TraceView tview) {
        if (tview == null) {
            IViewPart view = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().findView(TraceView.ID);
            if (!(view instanceof TraceView)) return null; // FIXME - this would be an internal error
            tview = (TraceView)view;
        }
        return tview.signature;
    }

    /** Creates (if needed) and returns the trace view, setting it to data for the most recent selection in the Proof View. */
    public void setTraceViewUI(/*@ nullable*/ TraceView tview, IJavaProject currentProject) {
        TreeItem ti = findView().selected;
        if (ti == null) return;
        OpenJMLView.Info info = (OpenJMLView.Info)ti.getData();
        if (info == null) return;
        IProverResult res = info.proofResult;
        String methodName = ti.getText();
        ICounterexample ce = res == null ? null : res.counterexample();
        String text = ce instanceof Counterexample ? ((Counterexample)ce).traceText : null;
        setTraceViewUI(tview, methodName, text, true);
    }

    public void setTraceView(final IJavaProject currentProject) {
        Display d = Display.getDefault();
        d.asyncExec(new Runnable() {
            public void run() {
                setTraceViewUI(null, currentProject);
            }
        });
    }

    public void setTraceView(final String key, final IJavaProject currentProject) {
        Display d = Display.getDefault();
        d.asyncExec(new Runnable() {
            public void run() {
                OpenJMLView view = Activator.utils().findView();
                final TreeItem ti = view.treeitems.get(key);
                view.selected = ti;
                setTraceViewUI(null, currentProject);
                // FIXME - highlight also
                OpenJMLView.Info info = (OpenJMLView.Info)ti.getData();
                if (info != null && info.javaElement instanceof IMethod) {
                    Activator.utils().getInterface(currentProject).highlightCounterexamplePath((IMethod)info.javaElement,info.proofResult,view.treece.get(ti));
                }

            }
        });
    }

    /**
     * This class is an implementation of the interfaces needed to provide input
     * to and launch editors in the workspace.
     * 
     * @author David R. Cok
     */
    public static class StringStorage implements IStorage, IStorageEditorInput {
        /** The initial content of the editor */
        private @NonNull
        String content;
        /** The name of storage unit (e.g. the file name) */
        private @NonNull
        String name;

        /** A constructor for a new storage unit */
        // @ assignable this.*;
        public StringStorage(@NonNull String content, @NonNull String name) {
            this.content = content;
            this.name = name;
        }

        /** Interface method that returns the contents of the storage unit */
        @Override
        public InputStream getContents() throws CoreException {
            return new ByteArrayInputStream(content.getBytes());
        }

        /**
         * Returns the path to the underlying resource
         * 
         * @return null (not needed for readonly Strings)
         */
        @Override
        public IPath getFullPath() {
            return null;
        }

        /**
         * Returns the name of the storage object
         * 
         * @return the name of the storage unit
         */
        @Override
        @Query
        public @NonNull
        String getName() {
            return name;
        }

        /**
         * Returns whether the storage object is read only
         * 
         * @return always true
         */
        @Override
        public boolean isReadOnly() {
            return true;
        }

        /**
         * Returns the object adapted to the given class. It appears we can
         * ignore this and always return null.
         * 
         * @return null
         */
        @Override
        @SuppressWarnings("rawtypes")
        // Can't add type parameters because the parent interface does not have
        // them
        public @Nullable
        Object getAdapter(@NonNull Class arg0) {
            return null;
        }

        /**
         * Returns self
         * 
         * @return this object
         */
        // @ ensures \return == this;
        @Override
        public IStorage getStorage() throws CoreException {
            return (IStorage) this;
        }

        /**
         * Returns whether the underlying storage object exists
         * 
         * @return always true
         */
        @Override
        public boolean exists() {
            return true;
        }

        /**
         * Returns an ImageDescriptor, here ignored
         * 
         * @return always null
         */
        @Override
        public ImageDescriptor getImageDescriptor() {
            return null;
        }

        /**
         * Returns a corresponding Persistable object, here ignored
         * 
         * @return always null
         */
        @Override
        public IPersistableElement getPersistable() {
            return null;
        }

        /**
         * Return the text desired in a tool tip, here the name of the storage
         * unit
         */
        @NonNull
        @Override
        public String getToolTipText() {
            return name;
        }

    }

    /**
     * Launches a read-only text editor with the given content and name
     * 
     * @param content
     *            the content of the editor
     * @param name
     *            the name (as in the title) of the editor
     */
    public void launchEditor(String content, String name) {
        try {
            IEditorInput editorInput = new StringStorage(content, name);
            IWorkbenchWindow window = PlatformUI.getWorkbench()
                                    .getActiveWorkbenchWindow();
            IWorkbenchPage page = window.getActivePage();
            page.openEditor(editorInput, "org.eclipse.ui.DefaultTextEditor");
        } catch (Exception e) {
            showExceptionInUI(null, "Failure while launching an editor", e);
        }
    }

    /**
     * Launches a read-only text editor with the given content and name
     * 
     * @param content
     *            the content of the editor
     * @param name
     *            the name (as in the title) of the editor
     */
    public void launchJavaEditor(String content, String name) {
        try {
            IEditorInput editorInput = new StringStorage(content, name);
            IWorkbenchWindow window = PlatformUI.getWorkbench()
                                    .getActiveWorkbenchWindow();
            IWorkbenchPage page = window.getActivePage();
            page.openEditor(editorInput, org.eclipse.jdt.ui.JavaUI.ID_CU_EDITOR);
        } catch (Exception e) {
            showExceptionInUI(null, "Failure while launching an editor", e);
        }
    }

    /**
     * Launches a editable Java editor with the given file
     * 
     * @param file
     *            the file to edit
     */
    public void launchJavaEditor(IFile file) {
        try {
            IFileEditorInput editorInput = new FileEditorInput(file);
            IWorkbenchWindow window = PlatformUI.getWorkbench()
                                    .getActiveWorkbenchWindow();
            IWorkbenchPage page = window.getActivePage();
            page.openEditor(editorInput, org.eclipse.jdt.ui.JavaUI.ID_CU_EDITOR);
        } catch (Exception e) {
            showExceptionInUI(null, "Failure while launching an editor", e);
        }
    }

    // public void launchJavaEditor(File file) {
    // try {
    // IFileStore fileStore = EFS.getLocalFileSystem().getStore();//new
    // Path(filterPath));
    // fileStore = fileStore.getChild(file.getAbsolutePath());
    // IFileEditorInput editorInput = new FileEditorInput(file);
    // IWorkbenchWindow window =
    // PlatformUI.getWorkbench().getActiveWorkbenchWindow();
    // IWorkbenchPage page = window.getActivePage();
    // page.openEditor(editorInput, org.eclipse.jdt.ui.JavaUI.ID_CU_EDITOR );
    // } catch (Exception e) {
    // showExceptionInUI(null,"Failure while launching an editor", e);
    // }
    // }

    /**
     * Deletes the markers in any of the objects in the List that are IResource
     * objects; if the object is a container, markers are deleted for any
     * resources in the container; other kinds of objects are ignored.
     * 
     * @param <T>
     *            just the type of the list
     * @param list
     *            a list of objects whose markers are to be deleted
     * @param shell
     *            the current shell for dialogs (or null for default)
     */
    public <T> void deleteMarkers(List<T> list, @Nullable Shell shell) {
        int maxdialogs = 5;
        for (T t : list) {
            if (!(t instanceof IResource))
                continue;
            IResource resource = (IResource) t;
            try {
                deleteMarkers(resource, shell);
            } catch (Exception e) {
                Log.errorlog("Exception while deleting markers: " + e, e);
                if ((maxdialogs--) > 0) {
                    showMessage(
                                            shell,
                                            "JML Plugin Exception",
                                            "Exception while deleting markers "
                                                                    + (resource != null ? "on "
                                                                                            + resource.getName() : "")
                                                                    + e.toString());
                }
            }
        }
    }

    /**
     * Deletes the markers (and highlighting) in the given resource; if the
     * object is a container, markers are deleted for any resources in the
     * container; other kinds of objects are ignored.
     * 
     * @param resource
     *            the resource whose markers are to be deleted
     * @param shell
     *            the current shell for dialogs (or null for default)
     */
    public void deleteMarkers(IResource resource, @Nullable Shell shell) {
        try {
            if (Options.uiverboseness)
                Log.log("Deleting markers in " + resource.getName());
            resource.deleteMarkers(Env.JML_MARKER_ID, false,
                                    IResource.DEPTH_INFINITE);
            resource.deleteMarkers(Env.ESC_MARKER_ID, false,
                                    IResource.DEPTH_INFINITE);
            resource.deleteMarkers(Env.JML_HIGHLIGHT_ID, false,
                                    IResource.DEPTH_INFINITE);
            resource.deleteMarkers(Env.JML_HIGHLIGHT_ID_TRUE, false,
                                    IResource.DEPTH_INFINITE);
            resource.deleteMarkers(Env.JML_HIGHLIGHT_ID_FALSE, false,
                                    IResource.DEPTH_INFINITE);
            resource.deleteMarkers(Env.JML_HIGHLIGHT_ID_EXCEPTION, false,
                                    IResource.DEPTH_INFINITE);
        } catch (CoreException e) {
            String msg = "Failed to delete markers on " + resource.getProject();
            Log.errorlog(msg, e);
            Utils.showMessage(shell, "JML Plugin Exception", msg + " - " + e);
        }
    }


    public void deleteHighlights(IResource resource, @Nullable Shell shell) {
        try {
            if (Options.uiverboseness)
                Log.log("Deleting highlights in " + resource.getName());
            resource.deleteMarkers(Env.JML_HIGHLIGHT_ID, false,
                                    IResource.DEPTH_INFINITE);
            resource.deleteMarkers(Env.JML_HIGHLIGHT_ID_TRUE, false,
                                    IResource.DEPTH_INFINITE);
            resource.deleteMarkers(Env.JML_HIGHLIGHT_ID_FALSE, false,
                                    IResource.DEPTH_INFINITE);
            resource.deleteMarkers(Env.JML_HIGHLIGHT_ID_EXCEPTION, false,
                                    IResource.DEPTH_INFINITE);
        } catch (CoreException e) {
            String msg = "Failed to delete highlights on " + resource.getProject();
            Log.errorlog(msg, e);
            Utils.showMessage(shell, "JML Plugin Exception", msg + " - " + e);
        }
    }

    // TODO _ needs more documentation

    //	public Map<IJavaProject, Set<IResource>> enabledMaps = new HashMap<IJavaProject, Set<IResource>>();
    //
    //	public Set<IResource> getSet(IJavaProject jp) {
    //		Set<IResource> set = enabledMaps.get(jp);
    //		if (set == null) {
    //			enabledMaps.put(jp, set = new HashSet<IResource>());
    //		}
    //		return set;
    //	}

    Set<IResource> getRacFiles(IJavaProject jp) {
        String encoded = PathItem.getEncodedPath(jp,Env.racKey);
        Set<IResource> items = new HashSet<IResource>();
        for (PathItem item: PathItem.parseAll(encoded)) {
            if (item instanceof ProjectPath) {
                IResource r = jp.getProject().findMember(((ProjectPath)item).projectRelativeLocation);
                items.add(r);
            }
        }
        return items;
    }

    void setRacFiles(IJavaProject jp, Set<IResource> items) {
        List<PathItem> paths = new LinkedList<PathItem>();
        for (IResource r: items) {
            paths.add(new ProjectPath(r.getProjectRelativePath().toString()));
        }
        String encoded = PathItem.concat(paths);
        PathItem.setEncodedPath(jp,Env.racKey,encoded);
    }

    public void racMark(boolean enable, ISelection selection,
                            IWorkbenchWindow window, @Nullable Shell shell) {
        List<IResource> res = getSelectedResources(selection, window, shell);
        final Map<IJavaProject, List<IResource>> sorted = sortByProject(res);
        for (final IJavaProject jp : sorted.keySet()) {
            Set<IResource> items = getRacFiles(jp);
            for (IResource r : sorted.get(jp)) {
                mark(enable, r, items);
            }
            setRacFiles(jp,items);
        }
    }

    protected void mark(boolean enable, IResource r, Set<IResource> set) {
        try {
            if (r instanceof IFolder) {
                if (enable)
                    set.add(r);
                else {
                    set.remove(r);
                    IPath p = new Path(getRacDir()).append(r.getProjectRelativePath());
                    p = p.removeFileExtension().addFileExtension(".class");
                    r.getProject().findMember(p).delete(true,null);
                }
                //				for (IResource rr : ((IFolder) r).members()) {
                //					mark(enable, rr, set);
                //				}
            } else if (r instanceof IFile) {
                if (r.getName().endsWith(Strings.javaSuffix)) {
                    if (enable)
                        set.add(r);
                    else {
                        set.remove(r);
                        IPath p = r.getProject().getProjectRelativePath().append(getRacDir()).append(r.getProjectRelativePath().removeFirstSegments(1));
                        p = p.removeFileExtension().addFileExtension("class");
                        IProject pr = r.getProject();
                        IResource rr = pr.findMember(p);
                        if (rr != null) rr.delete(true,null);
                    }
                }
            } else {
                // FIXME - needs an error message
                Log.log("Not handling " + r.getClass());
            }
        } catch (CoreException e) {
            Log.errorlog(
                                    "Core Exception while traversing Resource tree (mark for RAC)",
                                    e);
            // just continue
        }
    }

    public void highlight(final IResource r, final int finalOffset,
                            final int finalEnd, final int type) {
        // FIXME - I think this should be in the UI, not in a batch operation
        IWorkspaceRunnable runnable = new IWorkspaceRunnable() {
            public void run(IProgressMonitor monitor) throws CoreException {
                String name = type == IProverResult.Span.NORMAL ? Env.JML_HIGHLIGHT_ID
                                        : type == IProverResult.Span.TRUE ? Env.JML_HIGHLIGHT_ID_TRUE
                                                                : type == IProverResult.Span.FALSE ? Env.JML_HIGHLIGHT_ID_FALSE
                                                                                        : type == IProverResult.Span.EXCEPTION ? Env.JML_HIGHLIGHT_ID_EXCEPTION
                                                                                                                : Env.JML_HIGHLIGHT_ID;
                IMarker marker = r.createMarker(name);
                // marker.setAttribute(IMarker.LINE_NUMBER,
                // finalLineNumber >= 1? finalLineNumber : 1);
                // if (column >= 0) {
                marker.setAttribute(IMarker.CHAR_START, finalOffset);
                marker.setAttribute(IMarker.CHAR_END, finalEnd);
                // }
                // Note - it appears that CHAR_START is measured from the
                // beginning of the
                // file and overrides the line number when drawing the squiggly
                // The line number is used in the information about the problem
                // in
                // the Problem View

                // marker.setAttribute(IMarker.SEVERITY,b == null ? 0 : b ? 2 :
                // 1);
                // marker.setAttribute(IMarker.MESSAGE, finalErrorMessage);
            }
        };
        try {
            r.getWorkspace().run(runnable, r, IWorkspace.AVOID_UPDATE, null);
        } catch (CoreException e) {
            Log.errorlog("Core Exception while highlighting", e);
            // just continue
        }

    }

    public void racClear(ISelection selection, IWorkbenchWindow window,
                            final @Nullable Shell shell) {
        Collection<IJavaProject> res = getSelectedProjects(true,selection, window, shell);

        for (final IJavaProject jp : res) {
            Job j = new Job("JML Clear RAC") {
                public IStatus run(IProgressMonitor monitor) {
                    return racClear(jp,shell,monitor);
                }
            };
            // FIXME - use some proper scheduling rule?
            j.setRule(jp.getProject());
            j.setUser(true);
            j.schedule();
        }
    }

    public IStatus racClear(IJavaProject jp,
                            final @Nullable Shell shell, IProgressMonitor monitor) {
        boolean c = false;
        String racFolder = getRacDir();
        IFolder dir = jp.getProject().getFolder(racFolder);
        StringBuilder sb = new StringBuilder();
        try {
            for (IResource r : dir.members()) {
                try {
                    r.delete(IResource.FORCE,monitor);
                } catch (Exception e) {
                    sb.append(r.getName());
                    sb.append(" - ");
                    sb.append(e.getMessage());
                    sb.append(Env.eol);
                }
                if (monitor != null && monitor.isCanceled()) { c = true; break; }
            }
            if (sb.length() != 0) {
                showMessageInUI(shell, "OpenJML Exception",
                                        sb.toString());
            }
        } catch (CoreException e) {
            showMessageInUI(shell, "OpenJML Exception",
                                    e.getMessage());
        }
        return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
    }

    public void racChoose(ISelection selection, IWorkbenchWindow window,
                            final @Nullable Shell shell) {
        Collection<IJavaProject> res = getSelectedProjects(true,selection, window, shell);
        for (IJavaProject jp : res) {
            Dialog d = new RACDialog(shell,"Select files in " + jp.getElementName() + " for Runtime Assertion Checking",jp);
            d.create();
            d.open();
        }
    }

    //	protected void clear(IResource r, IFolder dir) {
    //		try {
    //			if (r instanceof IFolder) {
    //				for (IResource rr : ((IFolder) r).members()) {
    //					clear(rr, dir);
    //				}
    //			} else if (r instanceof IFile) {
    //				if (r.getName().endsWith(".java")) {
    //					ICompilationUnit cu = (ICompilationUnit) r
    //							.getAdapter(ICompilationUnit.class);
    //					if (cu != null) {
    //						for (IType t : cu.getTypes()) {
    //							String s = t.getFullyQualifiedName();
    //							s = s.replace('.', '/');
    //							s = s.substring(0, s.length() - (".java").length());
    //							s = s + ".class";
    //							IFile f = dir.getFile(s);
    //							f.delete(IResource.FORCE, null);
    //						}
    //					}
    //				}
    //			} else {
    //				if (Options.uiverboseness)
    //					Log.log("Not handling " + r.getClass());
    //			}
    //		} catch (CoreException e) {
    //			Log.errorlog(
    //					"Core Exception while traversing Resource tree (clear for RAC)",
    //					e);
    //			// just continue
    //		}
    //	}

    /**
     * Creates a map indexed by IJavaProject, with the value for each
     * IJavaProject being a Collection consisting of the subset of the argument
     * that belongs to the Java project.
     * 
     * @param elements
     *            The set of elements to sort
     * @return The resulting Map of IJavaProject to Collection
     */
    /*
     * @ requires elements != null; requires elements.elementType <: IResource
     * || elements.elementType <: IJavaElement; ensures \result != null;
     */
    public static @NonNull
    <T> Map<IJavaProject, List<T>> sortByProject(@NonNull Collection<T> elements) {
        Map<IJavaProject, List<T>> map = new HashMap<IJavaProject, List<T>>();
        Iterator<T> i = elements.iterator();
        while (i.hasNext()) {
            T o = i.next();
            IJavaProject jp;
            if (o instanceof IResource) {
                jp = JavaCore.create(((IResource) o).getProject());
            } else if (o instanceof IJavaElement) {
                jp = ((IJavaElement) o).getJavaProject();
            } else if (o instanceof IEditorInput) {
                // This option happens if the file is not in a Java project
                showMessageInUI(null,"OpenJML Error","To apply OpenJML tools, source files must be in Java projects, with a build environment set: " + ((IEditorInput)o).getName());
                continue;
            } else {
                Log.errorlog(
                                        "INTERNAL ERROR: Unexpected content for a selection List - "
                                                                + o.getClass(), null);
                continue;
            }
            if (jp != null && jp.exists())
                addToMap(map, jp, o);
        }
        return map;
    }

    /**
     * If key is not a key in the map, it is added, with an empty Collection for
     * its value; then the given object is added to the Collection for that key.
     * 
     * @param map
     *            A map of key values to Collections
     * @param key
     *            A key value to add to the map, if it is not already present
     * @param object
     *            An item to add to the Collection for the given key
     */
    private static <T> void addToMap(@NonNull Map<IJavaProject, List<T>> map,
                            @NonNull IJavaProject key, @NonNull T object) {
        List<T> list = map.get(key);
        if (list == null)
            map.put(key, list = new LinkedList<T>());
        list.add(object);
    }

    /**
     * Displays a message in a dialog in the UI thread - this may be called from
     * other threads.
     * 
     * @param shell
     *            The shell to use to display the dialog, or a top-level shell
     *            if the parameter is null
     * @param title
     *            The title of the dialog window
     * @param msg
     *            The message to display in the dialog
     */
    public static void showMessageInUI(@Nullable Shell shell,
                            @NonNull final String title, @NonNull final String msg) {
        final Shell fshell = shell;
        Display d = fshell == null ? Display.getDefault() : fshell.getDisplay();
        d.asyncExec(new Runnable() {
            public void run() {
                MessageDialog.openInformation(fshell, title, msg);
            }
        });
    }

    // Must already be in the UI thread
    public static boolean showConfirmInUI(@Nullable Shell shell,
                            @NonNull final String title, @NonNull final String msg) {
        final Shell fshell = shell;
        Display d = fshell == null ? Display.getDefault() : fshell.getDisplay();
        //		d.asyncExec(new Runnable() {
        //			public void run() {
        //				MessageDialog.openConfirm(fshell, title, msg);
        //			}
        //		});
        return MessageDialog.openConfirm(fshell, title, msg);
    }

    /** Pops up a dialog showing the given message and thte stack trace of the
     * given exception; may be called from the computational thread.
     */
    public static void showExceptionInUI(@Nullable Shell shell, String message,
                            Throwable e) {

        String emsg = e == null ? null : e.getMessage();
        if (emsg != null && !emsg.isEmpty()) message = message + " (" + emsg + ")"; //$NON-NLS-1$ //$NON-NLS-2$
        if (e != null) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            pw.println();
            e.printStackTrace(pw);
            message = message + Env.eol + sw.toString(); 
        }

        showMessageInUI(shell, "OpenJML Exception", message);
    }

    // FIXME - fix non-modal dialog
    /**
     * Displays a message in a non-modal dialog in the UI thread - this may be
     * called from other threads.
     * 
     * @param shell
     *            The shell to use to display the dialog, or a top-level shell
     *            if the parameter is null
     * @param title
     *            The title of the dialog window
     * @param msg
     *            The message to display in the dialog
     */
    public void showMessageInUINM(@Nullable Shell shell,
                            @NonNull final String title, @NonNull final String msg) {
        final Shell fshell = shell;
        Display d = fshell == null ? Display.getDefault() : fshell.getDisplay();
        d.asyncExec(new Runnable() {
            public void run() {
                Dialog d = new NonModalDialog(fshell, title, msg);
                d.open();
            }
        });
    }

    // FIXME this does not seem to be working
    static public class NonModalDialog extends MessageDialog {
        final static String[] buttons = { "OK" };

        public NonModalDialog(Shell shell, String title, String message) {
            super(new Shell(), title, null, message, INFORMATION, buttons, 0);
            setShellStyle(getShellStyle() | SWT.MODELESS);
            setBlockOnOpen(false);
        }
    }

    public final static QualifiedName SPECSPATH_ID = new QualifiedName(
                            Env.PLUGIN_ID, "specspath");
    public final static QualifiedName SOURCEPATH_ID = new QualifiedName(
                            Env.PLUGIN_ID, "sourcepath");


    /**
     * Displays a message in a information dialog; must be called from the UI
     * thread.
     * 
     * @param shell
     *            Either the parent shell
     * @param title
     *            A title for the dialog window
     * @param msg
     *            The message to display in the dialog window
     */
    // @ requires shell != null;
    // @ requires title != null;
    // @ requires msg != null;
    static public void showMessage(Shell shell, String title, String msg) {
        MessageDialog.openInformation(shell, title, msg);
    }

    // FIXME -document

    /**
     * Shows a dialog regarding an exception that has been thrown; this must be
     * called within the UI thread.
     */
    public void topLevelException(Shell shell, String title, Exception e) {
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        e.printStackTrace(pw);
        String s = "Please report this internal bug, along with information about the context that caused the problem:"
                                + Env.eol + Env.eol + sw.toString();
        final int maxlength = 2000; // Just a limit to keep from overfilling a
        // dialog box
        if (s.length() > maxlength) {
            s = s.substring(0, maxlength) + " ...";
        }
        showMessage(shell, "JML Top-level Exception: " + title, s);
    }

    /** The suffixes allowed for JML files. */
    static public final String[] suffixes = { ".jml", ".java" };

    /**
     * These constants should be the same as in org.jmlspecs.openjml.Utils, but
     * we don't reference them directly to avoid a dependency (in case we reuse
     * this plugin)
     */
    static public final int QUIET = 0;
    static public final int NORMAL = 1;
    static public final int PROGRESS = 2;
    static public final int VERBOSE = 3;
    static public final int DEBUG = 4;

    public int openjmlVerbose() {
        try {
            return Integer.valueOf(Options.value(Options.verbosityKey));
        } catch (NumberFormatException e) {
            return NORMAL;
        }
    }

    /**
     * This method returns an int giving the precedence of the suffix of the
     * file name: -1 indicates not a JML file; 0 is the preferred suffix;
     * increasing positive numbers indicate decreasing precedence of suffixes.
     * 
     * @param name
     *            the file name to be assessed
     * @return the precedence of the suffix (0 highest, more positive lower, -1
     *         is not JML)
     */
    @Pure
    static public int suffixOK(/* @ non_null */String name) {
        int i = 0;
        for (String s : suffixes) {
            if (name.endsWith(s))
                return i;
            i++;
        }
        return -1;
    }

    public String getRacDir() {
        String racdir = Options.value(Options.racbinKey);
        if (racdir == null || racdir.isEmpty()) racdir = "bin";
        return racdir;
    }

    /** Deletes the contents of the RAC binary directory (at the location defined in the
     * options) of the given project and refreshing it
     * in the workspace.  All done in the UI thread.
     * @param p the project whose RAC directory is to be cleaned
     */  // FIXME - should this be done in a computational thread, with a progress monitor?
    public void cleanRacbin(final IProject project) {
        Job job = new Job("Clean") { //$NON-NLS-1$
            public IStatus run(IProgressMonitor monitor) {
                try {
                    // FIXME - should we be using the preferences or the option?
                    String racbin = Activator.utils().getRacDir();
                    IResource rf = project.findMember(Options.value(Options.racbinKey));
                    if (rf instanceof IFolder) {
                        IFolder f = (IFolder)rf;
                        for (IResource r: f.members()) {
                            r.delete(IResource.FORCE,null);
                        }
                        f.refreshLocal(IResource.DEPTH_INFINITE,null);
                    } else {
                        // FIXME - error - show message
                    }
                } catch (CoreException e) {
                    Log.errorKey("openjml.ui.cleaning.rac",e); //$NON-NLS-1$
                }
                return Status.OK_STATUS;
            }
        };
        job.setUser(true);
        job.setRule(project);
        job.schedule();
    }

    public static final String RUNTIME_LIBRARY = Strings.runtimeJarName;

    /** Makes a classpath entry corresponding to the jmlruntime.jar library */
    public IClasspathEntry makeRuntimeLibEntry() {
        String envname = ClasspathVariableInitializer.OPENJML_RUNTIME_LIBRARY;
        IPath p = new Path(envname);
        IClasspathEntry libe = JavaCore.newVariableEntry(p,null,null);
        return libe;
    }

    /** Returns the value set against the runtime library classpath entry */
    public String fetchRuntimeLibEntry() {
        IPath p = JavaCore.getResolvedVariablePath(new Path(ClasspathVariableInitializer.OPENJML_RUNTIME_LIBRARY));
        String runtime = p == null ? null : p.toString();
        return runtime;
    }

    public int countMethods(IJavaProject jp) throws Exception {
        int count = 0;
        for (IPackageFragmentRoot pfr: jp.getPackageFragmentRoots()) {
            count += countMethods(pfr);
        }
        return count;
    }

    public int countMethods(IProject jp) throws Exception {
        return countMethods(JavaCore.create(jp));
    }

    public int countMethods(IPackageFragmentRoot pfr) throws Exception {
        int count = 0;
        for (IJavaElement pf: pfr.getChildren()) {
            if (pf instanceof IPackageFragment) {
                count += countMethods((IPackageFragment)pf);
            }
        }
        return count;
    }
    public int countMethods(List<?> elements) {
        int count = 0;
        for (Object r: elements) {
            try {
                if (r instanceof IPackageFragment) {
                    count += countMethods((IPackageFragment)r);
                } else if (r instanceof IJavaProject) {
                    count += countMethods((IJavaProject)r);
                } else if (r instanceof IProject) {
                    count += countMethods((IProject)r);
                } else if (r instanceof IPackageFragmentRoot) {
                    count += countMethods((IPackageFragmentRoot)r);
                } else if (r instanceof ICompilationUnit) {
                    count += countMethods((ICompilationUnit)r);
                } else if (r instanceof IType) {
                    count += countMethods((IType)r);
                } else if (r instanceof IMethod) {
                    count += 1;
                } else if (r instanceof IFile || r instanceof IFolder) {
                    // If a file is not part of a source folder, then we
                    // don't have Java elements and it is not a ICompilationUnit
                    // So we can't really count the methods in it.
                    // The number used here is arbitrary, and will result in
                    // a bad estimate of the work to be done. 
                    // TODO - count the methods using the OpenJML AST.
                    count += 1;
                } else {
                    Log.log("Can't count methods in a " + r.getClass());
                }
            } catch (Exception e) {
                // FIXME - record exception
            }
        }
        return count;
    }

    public int countMethods(IPackageFragment pf) throws Exception {
        int count = 0;
        for (ICompilationUnit cu: pf.getCompilationUnits()) {
            // getCompilationUnits() returns .jml and maybe other files as well
            if (cu.getPath().toString().endsWith(".java")) {
                count += countMethods(cu);
            }
        }
        return count;
    }

    public int countMethods(ICompilationUnit cu) throws Exception {
        int count = 0;
        for (IType t: cu.getTypes()) {
            count += countMethods(t);
        }
        return count;
    }

    public static class Counter extends JmlTreeScanner {

        int count = 0;

        public void visitJmlMethodDecl(JmlMethodDecl m) {
            count++;
            super.visitJmlMethodDecl(m);
        }

        public static int count(JCTree t) {
            Counter c = new Counter();
            t.accept(c);
            return c.count;
        }
    }

    public int countMethods(IResource f) throws Exception {
        int count = 0;
        if (f instanceof IFolder) {
            for (IResource r: ((IFolder)f).members()) {
                count += countMethods(r);
            }
        } else if (f instanceof IFile) {
            ICompilationUnit cu = (ICompilationUnit) f.getAdapter(ICompilationUnit.class);
            if (cu != null) count += countMethods(cu);
        } else {
            Log.log("Can't count a " + f.getClass());
        }
        return count;
    }

    public int countMethods(IType t) throws Exception {
        // FIXME - this does not count anonymous or local types or their methods
        int count = 0;
        IType[] types = t.getTypes();
        for (IType tt: types) {
            count += countMethods(tt);
        }
        IMethod[] methods = t.getMethods();
        boolean hasDeclaredConstructor = false;
        for (IMethod m : methods) {
            if (m.isConstructor()) { hasDeclaredConstructor = true; break; }
        }
        if (!hasDeclaredConstructor) count++;
        return methods.length + count;  
    }

    public int countMethods(IMethod m) throws Exception { 
        // Does not find local or anonymous classes
        return 1;
    }

    public int countMethods(IJavaElement f) {
        Log.log("Can't count a " + f.getClass());
        return 0;
    }

    // FIXME - have not been able to get this to work as I would like
    public static class ModelessDialog extends Dialog {
        public ModelessDialog(Shell parentShell) {
            super(parentShell);
            setBlockOnOpen(false);
        }

        protected void setShellStyle(int newShellStyle) {
            int newstyle = newShellStyle & ~SWT.APPLICATION_MODAL; /*
             * turn off
             * APPLICATION_MODAL
             */
            newstyle |= SWT.MODELESS; /* turn on MODELESS */

            super.setShellStyle(newstyle);
        }

        public int open() {
            int retVal = super.open();
            pumpMessages(); /*
             * this will let the caller wait till OK, Cancel is
             * pressed, but will let the other GUI responsive
             */
            return retVal;
        }

        protected void pumpMessages() {
            Shell sh = getShell();
            Display disp = sh.getDisplay();
            while (!sh.isDisposed()) {
                if (!disp.readAndDispatch())
                    disp.sleep();
            }
            disp.update();
        }
    }

}
