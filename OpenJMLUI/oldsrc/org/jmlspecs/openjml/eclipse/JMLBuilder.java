/*
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IResourceRuleFactory;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Main.Cmd;

// FIXME - we need to handle dependencies when doing incremental compilation
// FIXME - needs review - JMLBuilder
// FIXME - if there are multiple projects being run, they need to 
// be run in the right order 

// FIXME - review how timers are used


/** This class implements a builder for JML tools.  The builder is 
 *  run as part of the compilation cycle and appears in the list of
 *  builders under project properties.  It is enabled when the project 
 *  has a JML Nature.
 */
public class JMLBuilder extends IncrementalProjectBuilder {

    /** This class is used to walk the tree of incremental changes */
    static class DeltaVisitor implements IResourceDeltaVisitor {

        /** Local variable to store the resources to be built.  This list is
         * accumulated while walking the tree, and then the JML tools are activated
         * on the entire list at once.
         */
        private @NonNull List<IResource> resourcesToBuild = new LinkedList<IResource>();

        /*
         * (non-Javadoc)
         * 
         * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
         */
        public boolean visit(@NonNull IResourceDelta delta) throws CoreException {
            IResource resource = delta.getResource();
            //Log.log("Visiting (delta) " + resource);
            switch (delta.getKind()) {
            case IResourceDelta.ADDED:
                // handle added resource
                accumulate(resourcesToBuild,resource);
                break;
            case IResourceDelta.REMOVED:
                // handle removed resource
                break;
            case IResourceDelta.CHANGED:
                // handle changed resource
                accumulate(resourcesToBuild,resource);
                break;
            }
            //return true to continue visiting children.
            return true;
        }
    }

    /** This class is used to walk the tree of full build changes; collects all
     * files, recursively; does not delete markers. It ignores directories 
     * because the contents of the directory are automatically walked. */
    static class ResourceVisitor implements IResourceVisitor {
        /** Local variable to store the resources to be built.  This list is
         * accumulated while walking the tree, and then the JML tools are activated
         * on the entire list at once.
         */
        public @NonNull List<IResource> resourcesToBuild = new LinkedList<IResource>();

        public boolean visit(@NonNull IResource resource) {
            accumulate(resourcesToBuild,resource);
            //return true to continue visiting children.
            return true;
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.core.internal.events.InternalBuilder#build(int,
     *      java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
     */
    // The return value is used to indicate which other projects this project
    // would like delta data for the next time the builder is called.  A null value
    // for nothing other than one's own project is OK.
    @Override @Nullable
    protected IProject[] build(int kind, @Nullable Map<String,String> args, /*@ nullable */ IProgressMonitor monitor)
                            throws CoreException {
        // kind can be
        // FULL_BUILD - e.g. an automatic build after a request to clean
        //              or a manual request for a build after a manual clean
        // AUTO_BUILD - e.g. after a edit and save with auto building on
        // INCREMENTAL_BUILD - e.g. after an edit and save with auto building off,
        //                    and then a manual request to build
        // CLEAN_BUILD - does not call this method (calls clean(IProgressMonitor) instead)
        if (kind == FULL_BUILD || kind == CLEAN_BUILD) {
            fullBuild(monitor);
        } else { // INCREMENTAL_BUILD, as long as we have incremental information
            // AUTO_BUILD also (requires good dependency information)
            IResourceDelta delta = getDelta(getProject());
            if (delta == null) { // no delta available, do a full build
                fullBuild(monitor);
            } else {
                incrementalBuild(delta, monitor);
            }
        }
        return null;
    }


    /* (non-Javadoc)
     * @see org.eclipse.core.resources.IncrementalProjectBuilder#clean(org.eclipse.core.runtime.IProgressMonitor)
     */
    @Override
    protected void clean(/*@ nullable */ IProgressMonitor monitor) throws CoreException {
        if (Options.uiverboseness) Log.log("Cleaning: " + getProject().getName()); //$NON-NLS-1$
        IProject p = getProject();
        Activator.utils().deleteMarkers(p,null);
        Activator.utils().cleanRacbin(p);
    }

    /** Called during tree walking; it records the java files visited.
     * @param resourcesToBuild the list accumulated so far
     * @param resource the resource visited
     */
    static void accumulate(List<IResource> resourcesToBuild, IResource resource) {
        if (resource instanceof IFile) {
            String name = resource.getName();
            if (Utils.suffixOK(name) >= 0) {
                IFile file = (IFile) resource;
                resourcesToBuild.add(file);
            } else if (".classpath".equals(name)) { //$NON-NLS-1$
                resourcesToBuild.add(resource.getProject());
            }
        }
    }

    /** Perform actions on all identified items - called in UI thread
     * @param jproject the Java project all the resources are in
     * @param resourcesToBuild the resources to build
     * @param monitor the monitor to record progress and cancellation
     * @param full true if this is a full build, false if incremental
     */
    protected static void doAction(final IJavaProject jproject, final List<IResource> resourcesToBuild, IProgressMonitor monitor, boolean full) {
        // We've already checked that this is a Java and a JML project
        // Also all the resources should be from this project, because the
        // builders work project by project

        // These operations create new compilation contexts. Presumably this is
        // what is desired because either we are doing a full build from 
        // scratch or we are doing an incremental build in response to a
        // file save. In the latter case we will eventually want incremental
        // compilation, but since we don't have it yet, we have to do a new
        // compilation context.
        // Make a copy of the list because the list is used on a separate thread and 
        // might be cleared before it is finished processing.
        List<Object> list = new LinkedList<>();
        list.addAll(resourcesToBuild);
        boolean done = false;
        if (Options.isOption(Options.enableRacKey)) {
            Activator.utils().racMarked(jproject);
            done = true;
        } 
        if (Options.isOption(Options.enableESCKey)) {
            // FIXME - use monitor, be incremental?
            Activator.utils().checkESCProject(jproject,list,null,"Static Checks - Auto", null); //$NON-NLS-1$
            done = true;
        } 
        if (!done) {
            // If we did not already type-check because of RAC or ESC, do it now
            Activator.utils().getInterface(jproject).executeExternalCommand(Main.Cmd.CHECK,resourcesToBuild, monitor,true);
            //			Job j = new Job("OpenJML Auto Build") {
            //				public IStatus run(IProgressMonitor monitor) {
            //					monitor.beginTask("Static checking of " + jproject.getElementName(), 1);
            //					boolean c = false;
            //					try {
            //						Activator.utils().getInterface(jproject).executeExternalCommand(Main.Cmd.CHECK,resourcesToBuild, monitor,true);
            //					} catch (Exception e) {
            //						// FIXME - this will block, preventing progress on the rest of the projects
            //						Log.errorlog("Exception during Static Checking - " + jproject.getElementName(), e);
            //						Activator.utils().showExceptionInUI(null, "Exception during Static Checking - " + jproject.getElementName(), e);
            //						c = true;
            //					}
            //					return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
            //				}
            //			};
            //	        IResourceRuleFactory ruleFactory = 
            //	                ResourcesPlugin.getWorkspace().getRuleFactory();
            //			j.setRule(jproject.getProject());
            //			j.setUser(true); // true since the job has been initiated by an end-user
            //			j.schedule();
        }
    }


    /** Called when a full build is requested on the current project. 
     * @param monitor the progress monitor to use
     * @throws CoreException if something is wrong with the Eclipse resources
     */
    protected void fullBuild(final IProgressMonitor monitor) throws CoreException {
        IProject project = getProject();
        IJavaProject jproject = JavaCore.create(project);
        if (jproject == null || !jproject.exists()) {
            // It should not be possible to call the builder on a non-Java project.
            Log.errorKey("openjml.ui.building.non.java.project",null,project.getName()); //$NON-NLS-1$
            return;
        }

        if (Options.uiverboseness) Log.log("Full build " + project.getName()); //$NON-NLS-1$

        Timer.timer.markTime();
        Activator.utils().deleteMarkers(project,null);
        if (monitor.isCanceled() || isInterrupted()) {
            if (Options.uiverboseness) Log.log("Build interrupted"); //$NON-NLS-1$
            return;
        }
        ResourceVisitor v = new ResourceVisitor();
        for (IPackageFragmentRoot root : jproject.getAllPackageFragmentRoots()) {
            IResource res = root.getCorrespondingResource();
            if (res != null) res.accept(v);
        }
        //project.accept(v); - Calling accept on the project includes all of the files not on the source path - we don't want that
        // Don't clear if the rac directory is the bin directory
        String rd = Activator.utils().getRacDir();
        IPath rdd = jproject.getProject().findMember(rd).getFullPath(); // relative to workspace
        IPath output = jproject.getOutputLocation(); // also relative to workspace
        if (!rdd.equals(output)) {
            Activator.utils().racClear(jproject,null,monitor);
        }
        doAction(jproject,v.resourcesToBuild,monitor,true);
        v.resourcesToBuild.clear();
        if (Options.uiverboseness) Log.log(Timer.timer.getTimeString() + " Build complete " + project.getName()); //$NON-NLS-1$

    }

    /** Called when an incremental build is requested. 
     * @param delta the system supplied tree of changes
     * @param monitor the progress monitor to use
     * @throws CoreException if something is wrong with the Eclipse resources
     */
    protected void incrementalBuild(IResourceDelta delta,
                            IProgressMonitor monitor) throws CoreException {
        IProject project = getProject();
        IJavaProject jproject = JavaCore.create(project);
        if (jproject == null || !jproject.exists()) {
            // It should not be possible to call the builder on a non-Java project.
            Log.errorKey("openjml.ui.building.non.java.project",null,project.getName()); //$NON-NLS-1$
            return;
        }

        if (Options.uiverboseness) Log.log("Incremental build " + project.getName()); //$NON-NLS-1$
        Timer.timer.markTime();
        DeltaVisitor v = new DeltaVisitor();
        delta.accept(v);  // collects all changed files
        Activator.utils().deleteMarkers(v.resourcesToBuild,null);
        doAction(jproject,v.resourcesToBuild,monitor,false);
        v.resourcesToBuild.clear(); // Empties the list
        if (Options.uiverboseness) Log.log(Timer.timer.getTimeString() + " Build complete " + project.getName()); //$NON-NLS-1$

    }
}
