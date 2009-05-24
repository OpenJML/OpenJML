/*
 * Copyright (c) 2005 David R. Cok
 * @author David R. Cok
 * Created Aug 16, 2005
 */
package org.jmlspecs.openjml.eclipse;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaModel;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IProblemRequestor;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.WorkingCopyOwner;
//import org.jmlspecs.eclipse.jmlcl.JmlDriver;

/**
 * This class holds some global information relevant to the whole set of
 * types and compilation units being considered at a given time.  This 
 * information is collected here so that it is easier to pass it into 
 * various other classes and methods (without having to change API as
 * the content of this class changes).  Also, we make an object to hold
 * this information to avoid having the information be global, which would 
 * preclude having more than one project active at a given time.
 * <p>
 * In this context a 'project' is a set of compilation units, a classpath
 * (and thus the referenced material), and the options relevant to a JML
 * type checking operation.  The project may include a relevant IJavaProject.
 * Its lifetime may extend beyond a single typechecking operation in a 
 * GUI environment.
 */
public class ProjectInfo {
  // FIXME: At the moment the contents are referenced as public fields.
  // Use caution.

  /** A cached value of the workspace root. */
  static private IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();


  /**
   * A reference to the options (e.g. command-line options) for this project
   */
  //@ non_null
  public Options options;
  
  /**
   * The IProblemRequestor instance to which all problems (errors and
   * warnings) are reported.
   */
  //@ non_null
  public IProblemRequestor problemRequestor;
  
  /**
   * The IJavaProject that holds the compilation units and classpath material
   * relevant to this project.  Typically initialized by EclipseProjectCreator
   * or set in the process of setting up the ProjectInfostructure.
   */
  private IJavaProject jproject;
  
  /**
   * The IJavaProject holding source folders that point to the java files or
   * folders constituting the specspath.
   */
  public IJavaProject specsproject;
  
  /**
   * The folder used for RAC-generated source files within the IJavaProject.
   * Initialized by EclipseProjectCreator.  // FIXME - what about in UI case?
   */
  public IFolder racFolder;
  
  /**
   * The owner of all modified ASTs and source buffers.
   * Initialized in the constructor.
   */
  // FIXME - don't really want a new owner every creation of a ProjectInfo item - static?
  static final public WorkingCopyOwner owner = new WorkingCopyOwner() {};
  
  /** A map from Java project to the ProjectInfo structure that holds it; that
   * is, for any Java project jp, if map.get(jp) != null, then map.get(jp).jproject().equals(jp).
   */  // FIXME - not sure how to compare IJavaProject instances 
  static private Map<IJavaProject,ProjectInfo> map = new HashMap<IJavaProject,ProjectInfo>();

  /**
   * The database of type information for all the types encountered
   * in analyzing this project.
   * Initialized by setJavaProject().
   */
//  public Types types;

//  public Map<ICompilationUnit,CUInfo> cumap = new HashMap<ICompilationUnit,CUInfo>();
  
  /** A map from IFile (which is an IResource) to the CUInfo structure for that resource;
   * note that IResource equality is essentially equality on the IPath to the resource.
   */
//  public Map<IFile,CUInfo> resmap = new HashMap<IFile,CUInfo>();
  

  //public IResource[] classpathitems; // FIXME - do we need this one
  //public IResource[] sourcepathitems; // FIXME - do we need this one
  
//  /** An array of IResource objects holding the folders and files that
//   * constitute the specs path.
//   */
//  public IResource[] specspathitems;
  
  /**
   * Creates a new project instance, including a reference to the 
   * given set of command-line options.  Also initializes the 'owner'
   * field and problemRequestor fields. Other fields are not 
   * initialized and must be set explicitly.
   * @param options the command-line options
   * @param preq the problem requestor to use
   */
  //@ requires options != null;
  //@ ensures this.options == options;
  //@ ensures owner != null;
  public ProjectInfo(Options options, JmlProblemRequestor preq) {
    this.options = options;
    this.problemRequestor = preq;
    //owner = new WorkingCopyOwner() {};
    IProject p = root.getProject(options.specsProjectName);
    IJavaProject jp = JavaCore.create(p);
    if (jp != null && jp.exists()) {
      specsproject = jp;
    } else {
      // Don't worry if it does not exist.  In command-line mode it gets recreated
      // anyway.  In UI mode, we'll need to check and reconstruct if necessary.
      if (options.verbosity > 2) Log.log("No existing specs project found named " + options.specsProjectName);
    }
  }
  
  /** This call determines the appropriate specspath from the commandline options
   * and calls createSpecspathItems to setup the specs project.
   */
  public void initPaths() {
    String dirpath;
    if (options.specspath != null) {
      dirpath = options.specspath;
    } else {
      dirpath = options.classpath;
    }
//    try {
//         FIXME
//      String s = JmlDriver.internalspecs();
//      dirpath = dirpath.replace("##",s==null?"":s);
//    } catch (java.io.IOException e) {
//      JmlEclipseProblem.report(this.problemRequestor,
//              Problems.NOINTERNALSPECS,e);
//    }
    String[] items = dirpath.split(java.io.File.pathSeparator);
    createSpecspathFolders(items);
  }

  // FIXME - where does the specsProject get created - or deleted?
  /** Creates the source folders in the already existing specs project,
   * with one source folder per item in the argument; the source folders are
   * then made the classpath of the specs project.
   * @param items the set of specs path items, given as full absolute paths in
   * the local file system
   * @return null if all is well, an error message if not
   */
  //@ requires specsproject != null;
  public String createSpecspathFolders(/*@ non_null */String[] items) {
    reset();
    IFolder specsfolder = specsproject.getProject().getFolder(Env.specsContainerName);
    try {
      if (!specsfolder.exists()) specsfolder.create(true,true,null);
    } catch (CoreException e) {
      String msg = "Failed to create the specspath folder";
      Log.errorlog(msg,e);
      return msg;
    }
    List<IClasspathEntry> cpelist = new LinkedList<IClasspathEntry>();
    Set<IPath> directories = new HashSet<IPath>();
    int i = 0;
    String errors = "";
    for (String item: items) {
      try {
        item = item.trim();
        if (options.verbosity > 2) Log.log(Timer.getTimeString() +" Specspath element: " + item);
        if (item.length() == 0) continue;
        String specsFolderName = Env.specsFolderRoot + (++i);
        IFolder specFolder = specsfolder.getFolder(specsFolderName);

        java.io.File file = new java.io.File(item);
        IPath absolutePath = Path.fromOSString(item).makeAbsolute(); // OK for non-absolute strings? relative to working directory?
        if (!file.exists()) {
          String msg = Problems.IGNORED_SPECSPATH_ELEMENT.toString(item + " (does not exist)");
          JmlEclipseProblem.report(problemRequestor, Problems.IGNORED_SPECSPATH_ELEMENT, item + " (does not exist)");
          Log.errorlog(msg,null);
          errors = errors + Env.eol + msg;
          continue;
        } else if (file.isFile()) {
          IClasspathEntry icpe = (JavaCore.newLibraryEntry(absolutePath,null,null));
          // check for duplicates
          for (IClasspathEntry cpe: cpelist) {
            if (cpe.equals(icpe)) { 
              String msg = Problems.DUPLICATE_SPECSPATH.toString(item);
              JmlEclipseProblem.report(this.problemRequestor,
                      Problems.DUPLICATE_SPECSPATH,item);
              Log.errorlog(msg,null);
              icpe = null; 
              errors = errors + Env.eol + msg;
              break;
            }
          }
          if (icpe != null) {
            if (options.verbosity > 1) Log.log(Timer.getTimeString() + "      New library element " + item);
            cpelist.add(icpe);
          } else {
            continue;
          }

        } else if (file.isDirectory()) {
          if (directories.contains(absolutePath)) {
            String msg = Problems.DUPLICATE_SPECSPATH.toString(item);
            JmlEclipseProblem.report(this.problemRequestor,
                    Problems.DUPLICATE_SPECSPATH,item);
            Log.errorlog(msg,null);
            errors = errors + Env.eol + msg;
            continue;
          }
          directories.add(absolutePath);
          if (options.verbosity > 1) Log.log(Timer.getTimeString() + "      Linking " + specFolder + " -> " + absolutePath);
          
          try {
            // The call below will fail if the path cannot be linked to, which happens,
            // for example, if item == "." and there is no working directory set
            // Need a better error reporting mechanism in that case
            specFolder.createLink(absolutePath,IResource.ALLOW_MISSING_LOCAL,null);
            // The docs say the path here must be a workspace-absolute path
            IClasspathEntry icpe = JavaCore.newSourceEntry(specFolder.getFullPath());
            if (icpe != null) cpelist.add(icpe);
          } catch (Exception e) {
            String arg = "Failed to link in the specs path item " + item;
            JmlEclipseProblem.report(this.problemRequestor,
                    Problems.INTERNAL_ERROR,arg);
            Log.errorlog(arg,e);
            errors = errors + Env.eol + arg;
            continue;
          }

//        try {
//        IFolder ff = folder.getFolder(file.getName());
//        ff.createLink(p,IResource.NONE,null);
//        list.add(ff);
//        //Log.log("Linked to path element (file): " + p.toOSString());
//        } catch (CoreException e) {
//        JmlEclipseProblem.report(problemRequestor, Problems.INTERNAL_EXCEPTION,
//        "An exception occurred while calling IFolder.createLink on " + 
//        item + ", an element of the specspath",
//        e,Problems.exceptionStack(e));
//        Log.errorlog("Could not link to " + item,e);
//        }
        } else {
          errors += Env.eol + JmlEclipseProblem.report(problemRequestor, Problems.IGNORED_SPECSPATH_ELEMENT, 
                  item + " (exists, but is not a file or directory)");
          continue;
        }

      } catch (RuntimeException e) {
        errors += Env.eol + JmlEclipseProblem.report(this.problemRequestor,
                Problems.INTERNAL_ERROR,
                "Failed to initialize: " + e);
        e.printStackTrace();
        continue;
      }
    }
    
    try {
//      IClasspathEntry[] pentries = jproject.getRawClasspath();
//      for (IClasspathEntry icpe: pentries) {
//        cpelist.add(icpe);
//      }
      IClasspathEntry p = JavaCore.newProjectEntry(jproject.getProject().getFullPath());
      cpelist.add(p);
      // What if we are runing with -source 1.4 ? FIXME
      IPath pp = JavaCore.getClasspathVariable("JRE_LIB");
      if (pp != null) {
        IClasspathEntry icpe = JavaCore.newLibraryEntry(pp,null,null);
        for (IClasspathEntry icp: cpelist) {
          if (icp.equals(icpe)) {
            // JRE_LIB is already in cpelist - must have been explicitly
            // on the classpath.  setRawClasspath below fails if it is
            // in the list twice, so we check and avoid that situation here
            icpe = null;
            break;
          }
        }
        if (icpe != null) cpelist.add(icpe);
      } else {
        // FIXME
        Log.log("Could not find JRE_LIB");
      }

      // The following call fails if there are null entries; it also
      // fails if JRE_LIB is in more than once (and perhaps also if 
      // there are other duplicate entries as well).
      specsproject.setRawClasspath(cpelist.toArray(new IClasspathEntry[cpelist.size()]),null);
    } catch (JavaModelException e) {
      errors += Env.eol + JmlEclipseProblem.report(this.problemRequestor,
              Problems.ECLIPSE,
              "Failed to set the specspath " + e);
    }
//  if (options.verbosity>2) {
//  for (IResource rr: specsFolder.members()) {
//  Log.log("    Src folder: " + rr.getFullPath() + " -> " + rr.getLocation());
//  }
//  }


    return errors.length() == 0 ? null : errors;
  }
  
  // FIXME - will need to reset the cache whenever there are changes to the directory structure
  /** Deletes all cached information about the package locations - call this to
   * invalidate the cache when the specs path or the contents of its items changes.
   */
  public void reset() {
    specspathmap = new HashMap<String,List<IFolder>>();
  }

  /** This map contains a mapping from a dotted package name to a list of
   * IFolders that constitute the locations of files for that package in
   * the specs path.  It is thus a cached version of the specs path and is
   * invalid if the specs path changes or the content of the directory 
   * hierarchy for the specs path items changes.
   */
  private Map<String,List<IFolder>> specspathmap = new HashMap<String,List<IFolder>>();

//  /** Finds the first spec file for the given package and type, returning null
//   * if none was found on the specspath
//   * @param packageName the dot-separated type name
//   * @param typeName the type name
//   * @return an IFile for the specs file or null if none was found
//   */
//  public IFile findSpecsLeader(/*@ non_null */ String packageName, /*@ non_null */ String typeName) {
//    List<IFolder> locations = getLocations(packageName);
//    // FIXME - don't hard code the suffixes
//    for (IFolder location: locations) {
//      IFile f = location.getFile(typeName + ".refines-java");
//      if (f != null && f.exists()) return f;
//      f = location.getFile(typeName + ".refines-spec");
//      if (f != null && f.exists()) return f;
//      f = location.getFile(typeName + ".refines-jml");
//      if (f != null && f.exists()) return f;
//      f = location.getFile(typeName + ".java");
//      if (f != null && f.exists()) return f;
//      f = location.getFile(typeName + ".spec");
//      if (f != null && f.exists()) return f;
//      f = location.getFile(typeName + ".jml");
//      if (f != null && f.exists()) return f;
//    }
//    return null;
//  }
  
  
//  /** Returns the sequence of folders corresponding to the given package.
//   * @param packageName the dot-separated package name
//   * @return a List of IFolders corresponding to the package
//   */
//  // FIXME - what about stuff in jar files?
//  //@ non_null
//  public List<IFolder> getLocations(/*@ non_null */ String packageName) {
//    List<IFolder> locations = specspathmap.get(packageName);
//    if (locations != null) return locations;
//    IPath p = new Path(packageName.replaceAll("\\.", "/"));
//    locations = new LinkedList<IFolder>();
//    try {
//      IFolder sp = (IFolder)specsproject.getProject().findMember(Env.specsContainerName);
//      for (IResource item: sp.members()) {
//        if (item instanceof IContainer) {
//          IFolder f = ((IContainer)item).getFolder(p);
//          if (f != null && f.exists()) locations.add(f);
//        } else {
//          // FIXME
//          Log.log("Jar files not currently supported for specs: " + item.getName());
//        }
//      }
//    } catch (CoreException e) {
//      Log.errorlog("Could not handle specs path", e);
//    }
//    specspathmap.put(packageName, locations);
//    return locations;
//  }


//  /** Finds a given file (fileName includes a suffix) in the given package on
//   * the specs path, returning null if not found
//   * @param packageName the dot-separated package name
//   * @param fileName the name of the file to be found
//   * @return an IFile object for the found file, or null if not found
//   */
//  public IFile findSpecsFile(String packageName, String fileName) {
//    List<IFolder> locations = getLocations(packageName);
//    for (IFolder location: locations) {
//      IFile f = location.getFile(fileName);
//      if (f != null && f.exists()) return f;
//    }
//    return null;
//  }

  /** Sets the IJavaProject for the project.
   * @param jp The associated IJavaProject
   */
  //@ requires jp != null;
  //@ ensures jproject == jp;
  //@ ensures types != null && \fresh(types);
  //@ ensures types.jproject == jproject;
  public void setJavaProject(IJavaProject jp) {
    jproject = jp;
    map.put(jproject, this);
  }
  
  /** Returns a previously created ProjectInfo structure for which the
   * given JavaProject was set as its java project (using setJavaProject).
   * @param jp the Java project
   * @return the most recent ProjectInfo for which jp is the Java project
   */
  // FIXME - not entirely sure that this map works properly for independently
  // generated IJavaProject objects for a given project
  //@ ensures \result != null ==> \result.jproject().equals(jp);
  static public ProjectInfo getProjectInfo(/*@ non_null */ IJavaProject jp) {
    ProjectInfo p = map.get(jp);
    return p;
  }
  
  /** Returns the Java Project for this ProjectInfo structure
   * @return the Java project for this ProjectInfo structure
   */
  public IJavaProject jproject() { return jproject; }
  
  // FIXME - not used yet - is this the right thing to mark phases?
  //static public enum Status { INIT, PARSED, RESOLVED, TYPECHECKED }

  /** Checks if the suffix belongs to a spec file, returning -1 if not,
   * and non-negative if it does.  The result returned also indicates
   * the priority of the suffix,with lower numbers meaning higher
   * priority.
   * @param name the file name being checked
   * @return -1 if not a spec suffix, non-negative and indicating priority if it is
   */
  // FIXME - don't hard code this list, make it an option
  static public int suffixOK(/*@ non_null */ String name) {
    if (name.endsWith(".java")) return 3;
    if (name.endsWith(".spec")) return 4;
    if (name.endsWith(".jml")) return 5;
    if (name.endsWith(".refines-java")) return 0;
    if (name.endsWith(".refines-spec")) return 1;
    if (name.endsWith(".refines-jml")) return 2;
    return -1;
  }
  
//  /** Creates a new, empty Java project with the given name; if delete is true,
//   * any existing project is first deleted; if delete is false, it is kept (and the
//   * content also retained) if it is a Java project.
//   * @param tempProjectName the name of the new project
//   * @param delete whether to delete any existing project
//   * @param force whether to delete the project if it exists and is not a Java Project
//   * @return the new java project
//   */
//  //@ requires options != null;
//  //@ requires problemRequestor != null;
//  //@ requires root != null;
//  public IJavaProject createEmptyJavaProject(/*@ non_null */ String tempProjectName, boolean delete, boolean force) {
//    try {
//
//      // Get the environment
//      IJavaModel jmodel = JavaCore.create(root);
//
//      IProject project = root.getProject(tempProjectName);
//
//      // Does it exist already?
//      if (!delete) {
//        if (project != null && project.exists()) {
//          IJavaProject j = JavaCore.create(project);
//          if (j != null && j.exists()) return j;
//          // The project exists, but is not a Java Project, so we
//          // have to delete it and construct it
//          if (!force) return null;
//        }
//      }
//      
//      // TODO - If we know this is truly a temporary workspace, we can 
//      // simply call delete on the workspace
//
//      // Delete any directory where we want to put the temporary project.
//      // Do this because the getProject call below can trigger compilation,
//      // if not other activities depending on the settings of the project.
//      if (options.verbosity > 2) Log.log(Timer.getTimeString() + " Deleting temporary project " + tempProjectName);
//      if (project != null) { // Should never be null, even if the project does not exist
//        project.delete(true,null);
//        project.refreshLocal(IResource.DEPTH_INFINITE,null);
//        if (project.exists()) {
//          String msg = project.getLocation() + " still exists after having been deleted.";
//          JmlEclipseProblem.report(problemRequestor,
//                  Problems.INTERNAL_ERROR,msg);
//          Log.errorlog(msg,null);
//          // Perhaps should return, but will try for now to continue anyway
//        }
//      }
//
//      // Create and open a java project
//
//      if (options.verbosity > 2) Log.log(Timer.getTimeString() + " Recreating temporary project " + tempProjectName);
//      project = root.getProject(tempProjectName);
//      project.create(null);
//      project.open(null);
//      if (options.verbosity > 2) Log.log(Timer.getTimeString() + " Setting project characteristics");
//      String[] natures = new String[]{org.eclipse.jdt.core.JavaCore.NATURE_ID};
//      IProjectDescription desc = project.getDescription();
//      desc.setNatureIds(natures);
//      desc.setBuildSpec(new ICommand[0]);
//      project.setDescription(desc,null);
//      // In a separate step we turn off the Java Builder.  It appears that setting
//      // the Java Nature automatically turns on the Java Builder, even if the 
//      // build spec is set at the same time.  So we do it in a second step
//      // (and cross our fingers).
//      desc = project.getDescription();
//      desc.setBuildSpec(new ICommand[0]);
//      project.setDescription(desc,null);
//
//      // Set the project options to control the compiler
//      // - FIXME need a way to incorporate the users preferences for compiler warnings
//
//      IJavaProject javaproject = jmodel.getJavaProject(tempProjectName);
//      if (options.verbosity > 2) Log.log(Timer.getTimeString() + " Setting project options");
//      // This keeps task tags from being reported as problems
//      javaproject.setOption(JavaCore.COMPILER_TASK_TAGS,"");
//      // Sets the level of source code being recognized
//      javaproject.setOption(JavaCore.COMPILER_SOURCE,Env.jlsLevel.sourceLevel());
//      // Turns off the parsing of Javadoc comments, since we are not going to
//      // use the tags (TODO - change this if we are going to implement jmldoc)
//      javaproject.setOption(JavaCore.COMPILER_DOC_COMMENT_SUPPORT,"disabled");
//      // Turns off the cleaning of the output directory
//      javaproject.setOption(JavaCore.CORE_JAVA_BUILD_CLEAN_OUTPUT_FOLDER,"ignore");
//      // Avoids copying stuff to the output directory
//      javaproject.setOption(JavaCore.CORE_JAVA_BUILD_RESOURCE_COPY_FILTER,"*");
//
//      return javaproject;
//
//    } catch (CoreException e) {
//      String msg = "Failed to initialize the specifications project: " + e;
//      JmlEclipseProblem.report(this.problemRequestor,
//              Problems.INTERNAL_ERROR,
//              msg);
//      Log.errorlog(msg,e);
//      return null;
//    } catch (RuntimeException e) {
//      String msg = "Failed to initialize the specifications project: " + e;
//      JmlEclipseProblem.report(this.problemRequestor,
//              Problems.INTERNAL_ERROR,
//              msg);
//      Log.errorlog(msg,e);
//      return null;
//    }
//  }
}
