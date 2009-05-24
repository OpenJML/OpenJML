package org.jmlspecs.openjml.eclipse;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.internal.core.JavaModelManager;
import org.jmlspecs.annotations.*;

// FIXME - we need to handle dependencies when doing incremental compilation

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
   * files, recursively; does not delete markers. */
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
  public static final String JML_BUILDER_ID = Activator.PLUGIN_ID + ".JMLBuilder";

  /** The ID of the marker, which must match that in the plugin file. */
  final static String JML_MARKER_ID = Activator.PLUGIN_ID + ".JMLProblem";

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
  protected IProject[] build(int kind, @Nullable Map/*<String,String>*/ args, IProgressMonitor monitor)
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
    Log.log("Cleaning: " + getProject().getName());
    deleteMarkers(getProject(),true);
  }


  /** Called during tree walking; it records the java files visited and
   *  deletes any markers.
   * @param resourcesToBuild the list accumulated so far
   * @param resource the resource visited
   * @param delete if true, markers are deleted as we walk the tree
   */
  static void accumulate(List<IResource> resourcesToBuild, IResource resource, boolean delete) {
    if (!(resource instanceof IFile)) return;
    String name = resource.getName();
    if (ProjectInfo.suffixOK(name) >= 0) {
      IFile file = (IFile) resource;
      resourcesToBuild.add(file);
      if (delete) deleteMarkers(file,false);
    }
  }
  
  // FIXME _ fix the number of tasks in a monitor

  /** Perform JML checking on all identified items - called in UI thread
   * @param jproject the Java project all the resources are in
   * @param resourcesToBuild the resources to build
   * @param monitor the monitor to record progress and cancellation
   */
  static void doChecking(IJavaProject jproject, List<IResource> resourcesToBuild, IProgressMonitor monitor) {
    Options options = Activator.options;
    // We've already checked that this is a Java and a JML project
    // Also all the resources should be from this project, because the
    // builders work project by project
    
    ProjectInfo pi = new ProjectInfo(options,preq);
    pi.setJavaProject(jproject);
    pi.specsproject = JavaCore.create(ResourcesPlugin.getWorkspace().getRoot().getProject("specsProject"));
    pi.racFolder = null; // FIXME - ???
    (new OpenJMLInterface(pi)).executeExternalCommand(OpenJMLInterface.Cmd.CHECK,resourcesToBuild, monitor);

    // FIXME - do we really want to work on compilation units -associated with working copies?
    
    //    
//    ICompilationUnit[] cus = new ICompilationUnit[resourcesToBuild.size()];
//    int i = 0;
//    for (IResource item: resourcesToBuild) {
//      IJavaElement e = JavaModelManager.create(item,jproject);
//      // NOTE: The call above creates a "handle-only" Java element.
//      // The resulting element may not actually exist.
//      Log.log("JML: " + item );
//      // FIXME - check this cast
//      cus[i++] = (ICompilationUnit)e;
//    }
//    Log.log(Timer.getTimeString() + " Starting actual JML checking");
//    try {
//      // FIXME- this recreates the ASTs - can we avoid that?
//      (new OpenJMLInterface(pi)).doProcessing(cus, monitor);
//    } catch (Exception e) {
//      Log.errorlog("Failure during JML checking " + e,e);
//    }
  }
  
  /** This holds an instance of an IProblemRequestor, implemented to
   * convert problems returned by JML checking into markers to be persisted
   * and displayed by the Eclipse workbench.
   */
  final static public JmlProblemRequestor preq = new JmlProblemRequestor() {
    public void acceptProblem(/*@ non_null */ IProblem p) {
      // JML checking produces CompilerProblems (in OpenJMLInterface); 
      // Eclipse produces other kinds of problems
      // stuff; Eclipse problems are already reported, so don't report them 
      // over again if JML encounters it as part of getting the Java AST
      if (!(p instanceof JmlEclipseProblem)) {
        int id = p.getID();
        if (!(id == IProblem.MethodRequiresBody || id == IProblem.UninitializedBlankFinalField)) return;
        String s = new String(p.getOriginatingFileName());
        if (s.endsWith(".java")) return;
//        Log.log("JAVA Problem: " + id + " " + new String(p.getOriginatingFileName()) + " " + p.getMessage());
//        p.delete();
        return;
      }
      if (p.isWarning() && level == 2) return;

      try {
        IResource f = null;
        char[] ch = p.getOriginatingFileName();
        IWorkspace w = ResourcesPlugin.getWorkspace();
        IWorkspaceRoot root = w.getRoot();
        if (ch != null) {
          Path path = new Path(new String(ch));
          f = root.findMember(path);
        } else {
          // No originating file name, so use the workspace root
          // FIXME - mihgt be better to use the project, if it were available
          f = root;
        }
        // Use the following if you want problems printed to the console
        // as well as producing markers and annotations
        //JmlEclipseProblem.printProblem(Log.log.stream(), p);

        final IResource r = f;
        final int finalLineNumber = p.getSourceLineNumber();
        final int column = p.getSourceStart();
        final int finalOffset = p.getSourceStart() + ((JmlEclipseProblem)p).lineStart;
        final int finalEnd = p.getSourceEnd() + 1 + ((JmlEclipseProblem)p).lineStart;
        final String finalErrorMessage = p.getMessage();
        final int finalSeverity = 
          p.isError() ? IMarker.SEVERITY_ERROR :
          p.isWarning() ? IMarker.SEVERITY_WARNING :
            IMarker.SEVERITY_INFO;

        // FIXME - perhaps should do all the markers for a given file at once for performance sake

        // Eclipse recommends that things that modify the resources
        // in a workspace be performed in a IWorkspaceRunnable
        IWorkspaceRunnable runnable = new IWorkspaceRunnable() {
          public void run(IProgressMonitor monitor) throws CoreException {
            IMarker marker = r.createMarker(JML_MARKER_ID);
            marker.setAttribute(IMarker.LINE_NUMBER, 
                    finalLineNumber >= 1? finalLineNumber : 1);
            if (column >= 0) {
              marker.setAttribute(IMarker.CHAR_START, finalOffset); 
              marker.setAttribute(IMarker.CHAR_END, finalEnd);
            }
            // Note - it appears that CHAR_START is measured from the beginning of the
            // file and overrides the line number

            marker.setAttribute(IMarker.SEVERITY,finalSeverity);
            marker.setAttribute(IMarker.MESSAGE, finalErrorMessage);
          }
        };
        r.getWorkspace().run(runnable, null);

        //addMarker(f,p.getMessage(),p.getSourceLineNumber(),IMarker.SEVERITY_WARNING);
      } catch (Exception e) {
        Log.errorlog("Failed to make a marker " + e,e);
      }
    }
  };


  /** Called when a full build is requested on the current project. 
   * @param monitor the progress monitor to use
   * @throws CoreException if something is wrong with the Eclipse resources
   */
  protected void fullBuild(final IProgressMonitor monitor) throws CoreException {
    IProject project = getProject();
    IJavaProject jproject = JavaCore.create(project);
    if (jproject == null || !jproject.exists()) {
      // It should not be possible to call the builder on a non-Java project.
      Log.errorlog("JMLBuilder has been invoked on a non-Java Project - " + project.getName(), null);
      return;
    }

    Log.log("Full build " + project.getName());
    Timer.markTime();
    deleteMarkers(project,true);
    if (monitor.isCanceled() || isInterrupted()) { // FIXME - is this the proper use of isInterrupted?
        Log.log("Build interrupted");
        return;
    }
    ResourceVisitor v = new ResourceVisitor();
    project.accept(v);
    doChecking(jproject,v.resourcesToBuild,monitor);
    v.resourcesToBuild.clear();
  }

  /** Called to do a build on a resource, recursively; this is a utility
   * to be called by client code elsewhere in the program.
   * @param jp the java project to which the resources belong 
   * @param resources the resources to JML check, each one recursively
   * @param monitor the progress monitor on which to report progress
   * @return true if the build was cancelled
   * @throws CoreException when the JML model is out of whack
   */
  static public boolean doBuild(IJavaProject jp, List<IResource> resources, IProgressMonitor monitor) throws CoreException {
    ResourceVisitor v = new ResourceVisitor();
    for (IResource r: resources) {
      r.accept(v);
    }
    monitor.beginTask("JML Manual Build", 
            5*v.resourcesToBuild.size());
    doChecking(jp,v.resourcesToBuild,monitor);
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
    Log.log("Incremental build " + project.getName());
    Timer.markTime();
    DeltaVisitor v = new DeltaVisitor();
    delta.accept(v);  // collects all changed files and deletes markers
    doChecking(JavaCore.create(getProject()),v.resourcesToBuild,monitor);
    v.resourcesToBuild.clear(); // Empties the list
  }
  
  /** Deletes all JML problem markers on the given resource 
   * 
   * @param resource the resource whose markers are to be deleted
   * @param recursive if true, resources contained in the first argument,
   *                recursively, also have markers deleted; if false, only
   *                this specific resource has markers deleted
   */
  static public void deleteMarkers(IResource resource, boolean recursive) {
    try {
      resource.deleteMarkers(JML_MARKER_ID, false, 
              recursive? IResource.DEPTH_INFINITE :IResource.DEPTH_ZERO);
    } catch (CoreException e) {
      Log.errorlog("Failed to delete markers on " + resource.getName(), e);
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
      Timer.markTime();
      deleteMarkers(resources,true); // FIXME - should this be done in another thread?  but it has to be completed before the checking starts
                  // FIXME - need to build one project at a time
      try {
          boolean cancelled = doBuild(JavaCore.create(((IResource)resources.get(0)).getProject()),resources, monitor);  // FIXME - build everything or update?
          Log.log(Timer.getTimeString() + " Manual build " + (cancelled ? "cancelled" : "ended"));
      } catch (CoreException e) {
          Log.errorlog("CoreException occurred during JML check ",e);
      }
      return false;
  }
  
  // FIXME - timer is used here in background threads
  // FIXME - should we call doBuild with groups of resources in the same project
  
}
