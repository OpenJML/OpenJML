/*
 * This file is part of the OpenJML project.
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
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.Main;

// FIXME - we need to handle dependencies when doing incremental compilation
// FIXME - needs review - JMLBuilder

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
				accumulate(resourcesToBuild,resource,true);
				break;
			case IResourceDelta.REMOVED:
				// handle removed resource
				break;
			case IResourceDelta.CHANGED:
				// handle changed resource
				accumulate(resourcesToBuild,resource,true);
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
			accumulate(resourcesToBuild,resource,false);
			//return true to continue visiting children.
			return true;
		}
	}

	/** The ID of the Builder, which must match that in the plugin file */
	public static final String JML_BUILDER_ID = Activator.PLUGIN_ID + ".JMLBuilder"; //$NON-NLS-1$

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
	protected IProject[] build(int kind, @Nullable Map<String,String> args, IProgressMonitor monitor)
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
			if (delta == null) {
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
	protected void clean(IProgressMonitor monitor) throws CoreException {
		if (Utils.verboseness >= Utils.NORMAL) Log.log("Cleaning: " + getProject().getName()); //$NON-NLS-1$
		deleteMarkers(getProject(),true);
		cleanRacbin(getProject());
	}

	// FIXME - move to Utils?
	
	/** Deletes the contents of the RAC binary directory (at the location defined in the
	 * options) of the given project and refreshing it
	 * in the workspace.  All done in the UI thread.
	 * @param p the project whose RAC directory is to be cleaned
	 */  // FIXME - should this be done in a computational thread, with a progress monitor?
	public void cleanRacbin(IProject p) {
		try {
			IPath path = new Path(Options.value(Options.racbinKey));
			IFolder f = (IFolder)p.findMember(path);
			for (IResource r: f.members()) {
				r.delete(IResource.FORCE,null);
			}
			f.refreshLocal(IResource.DEPTH_INFINITE,null);
		} catch (CoreException e) {
			Log.errorKey("openjml.ui.cleaning.rac",e); //$NON-NLS-1$
		}
	}


	/** Called during tree walking; it records the java files visited and
	 *  deletes any markers.
	 * @param resourcesToBuild the list accumulated so far
	 * @param resource the resource visited
	 * @param delete if true, markers are deleted as we walk the tree
	 */
	static void accumulate(List<IResource> resourcesToBuild, IResource resource, boolean delete) {
		if (resource instanceof IFile) {
			String name = resource.getName();
			if (Utils.suffixOK(name) >= 0) {
				IFile file = (IFile) resource;
				resourcesToBuild.add(file);
				if (delete) deleteMarkers(file,false);
			} else if (".classpath".equals(name)) { //$NON-NLS-1$
				resourcesToBuild.add(resource.getProject());
			}
		}
	}

	// FIXME _ fix the number of tasks in a monitor

	/** Perform JML checking on all identified items - called in UI thread
	 * @param jproject the Java project all the resources are in
	 * @param resourcesToBuild the resources to build
	 * @param monitor the monitor to record progress and cancellation
	 */
	protected static void doAction(IJavaProject jproject, List<IResource> resourcesToBuild, IProgressMonitor monitor) {
		// We've already checked that this is a Java and a JML project
		// Also all the resources should be from this project, because the
		// builders work project by project

		if (Options.isOption(Options.enableRacKey)) {
			Activator.getDefault().utils.doBuildRac(jproject,resourcesToBuild,monitor);
		} else {
			//doChecking(jproject,v.resourcesToBuild,monitor);
			if (Options.isOption(Options.autoAddRuntimeToProjectKey)) Activator.getDefault().utils.addRuntimeToProjectClasspath(jproject);
			Activator.getDefault().utils.getInterface(jproject).executeExternalCommand(Main.Cmd.CHECK,resourcesToBuild, monitor);
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

		if (Utils.verboseness >= Utils.NORMAL) Log.log("Full build " + project.getName()); //$NON-NLS-1$
		
		Timer.timer.markTime(); // FIXME - where is this timer used
		deleteMarkers(project,true);
		if (monitor.isCanceled() || isInterrupted()) {
			if (Utils.verboseness >= Utils.NORMAL) Log.log("Build interrupted"); //$NON-NLS-1$
			return;
		}
		ResourceVisitor v = new ResourceVisitor();
		project.accept(v);
		Activator.getDefault().utils.racClear(jproject,null,monitor);
		doAction(jproject,v.resourcesToBuild,monitor);
		v.resourcesToBuild.clear();
		if (Utils.verboseness >= Utils.NORMAL) Log.log(Timer.timer.getTimeString() + " Build complete " + project.getName()); //$NON-NLS-1$
	}
	
	// FIXME - move this to Utils? Combine into the one caller?

	/** Called to do a build on a list of resources; this is a utility
	 * to be called by client code elsewhere in the program.
	 * @param jproject the java project to which the resources belong 
	 * @param resources the resources to JML check, each one recursively
	 * @param monitor the progress monitor on which to report progress
	 * @return true if the build was cancelled
	 * @throws CoreException when the JML model is out of whack
	 */
	static public boolean doBuild(IJavaProject jproject, List<IResource> resources, 
			IProgressMonitor monitor) throws CoreException {
		ResourceVisitor v = new ResourceVisitor();
		for (IResource r: resources) {
			r.accept(v);
		}
		monitor.beginTask(Messages.OpenJMLUI_JMLBuilder_Title, 
				5*v.resourcesToBuild.size());
		if (Options.isOption(Options.autoAddRuntimeToProjectKey)) Activator.getDefault().utils.addRuntimeToProjectClasspath(jproject);
		Activator.getDefault().utils.getInterface(jproject).executeExternalCommand(Main.Cmd.CHECK,v.resourcesToBuild, monitor);
		boolean cancelled = monitor.isCanceled();
		monitor.done();
		v.resourcesToBuild.clear();
		return cancelled;
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

		if (Utils.verboseness >= Utils.NORMAL) Log.log("Incremental build " + project.getName()); //$NON-NLS-1$
		Timer.timer.markTime(); // FIXME - where is this timer used
		DeltaVisitor v = new DeltaVisitor();
		delta.accept(v);  // collects all changed files and deletes markers
		doAction(jproject,v.resourcesToBuild,monitor);
		v.resourcesToBuild.clear(); // Empties the list
		if (Utils.verboseness >= Utils.NORMAL) Log.log(Timer.timer.getTimeString() + " Build complete " + project.getName()); //$NON-NLS-1$
	}

	// FIXME - duplicated in Utils?
	
	/** Deletes all JML problem markers on the given resource 
	 * 
	 * @param resource the resource whose markers are to be deleted
	 * @param recursive if true, resources contained in the first argument,
	 *                recursively, also have markers deleted; if false, only
	 *                this specific resource has markers deleted
	 */
	static public void deleteMarkers(IResource resource, boolean recursive) {
		try {
			resource.deleteMarkers(Utils.JML_MARKER_ID, false, 
					recursive? IResource.DEPTH_INFINITE :IResource.DEPTH_ZERO);
			resource.deleteMarkers(Utils.ESC_MARKER_ID, false, 
					recursive? IResource.DEPTH_INFINITE :IResource.DEPTH_ZERO);
		} catch (CoreException e) {
			Log.errorKey("openjml.ui.failed.to.delete.markers", e, resource.getName()); //$NON-NLS-1$
		}
	}

	/** Deletes all JML problem markers on the given resources 
	 * 
	 * @param resources the resources whose markers are to be deleted
	 * @param recursive if true, resources contained in the first argument,
	 *                recursively, also have markers deleted; if false, only
	 *                this specific resource has markers deleted
	 */
	static public void deleteMarkers(List<? extends IResource> resources, boolean recursive) {
		for (IResource r: resources) deleteMarkers(r,recursive);
	}


	// FIXME - if there are multiple projects being run, they need to 
	// be run in the right order 

	/** Checks the JML in each of the given resources, in order;
	 * expects to be called in the UI thread.
	 * @param resources the list of resources to check
	 * @param monitor the monitor to use to report progress and check for
	 *                cancellation
	 * @return true if the checking was cancelled
	 */
	static public boolean checkJML(List<IResource> resources, IProgressMonitor monitor) {
		if (resources.isEmpty()) return true;
		Timer.timer.markTime();
		deleteMarkers(resources,true); // FIXME - should this be done in another thread?  but it has to be completed before the checking starts
		// FIXME - need to build one project at a time
		try {
			boolean cancelled = doBuild(JavaCore.create(resources.get(0).getProject()),resources, monitor);  // FIXME - build everything or update?
			if (Utils.verboseness >= Utils.NORMAL) Log.log(Timer.timer.getTimeString() + " Manual build " + (cancelled ? "cancelled" : "ended")); //$NON-NLS-3$
		} catch (Exception e) {
			Log.errorKey("openjml.ui.exception.during.check",e); //$NON-NLS-1$
		}
		return false;
	}

	// FIXME - timer is used here in background threads

}
