/*
 * This file is part of the OpenJML plugin project. 
 * Copyright 2006-2009 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.Map;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IProblemRequestor;
import org.eclipse.jdt.core.compiler.IProblem;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.SpecPublic;

// TODO - The plugin tool reports problems by directly calling an instance
// of this IProblemRequestor.  The Eclipse framework actually uses
// a combination of a ProblemReporter to which problems are reported
// and requestors that can subscribe to problem reports.  Perhaps we
// should correct to that model.

/**
 * This is an implementation of the IProblemRequestor
 * interface as used in this application.  Upon receiving problem
 * reports (by calls of acceptProblem), it creates and records an Eclipse
 * problem marker specific to this plugin.
 */
/*
 * It also adds this bit of functionality - the ability to provide a mapping from 
 * IFile paths to working copies so that the right source text 
 * can be associated with a given problem message without having
 * to be sure that potential changes are written to disk.
 * TODO - this is not used at present, but is left in for now in case we 
 * implement this later.
 */
public class JmlProblemRequestor implements IProblemRequestor {
  
  /**
   * This is a map of filename to compilation unit.
   * The filename is gotten from IResource.getFullPath().toString().  
   * The compilation unit is typically a working copy, not necessarily 
   * saved to disk. Its text information can be obtained from 
   * getSource() after reconciliation.
   */
  private Map<String,ICompilationUnit> map = null;
  
  /** The Eclipse project associated with this problem requestor */
  @SpecPublic @Nullable 
  protected IProject project;
  
  /**
   * Returns the ICompilationUnit corresponding to the given path,
   * or null if none found
   * @param p the path used as a key
   * @return the associated ICompilationUnit
   */
  public @Nullable ICompilationUnit getICU(String p) {
    return map == null ? null : map.get(p);
  }

  /** Creates a problem requestor for a particular java project.  */
  public JmlProblemRequestor(@Nullable IJavaProject jp) {
      this.project = jp == null ? null : jp.getProject();
  }
  
  IProblem mostRecentProblem = null;
  
  /** Eclipse calls this when a problem is reported
   * @param p the reported problem
   * @see org.eclipse.jdt.core.IProblemRequestor#acceptProblem(org.eclipse.jdt.core.compiler.IProblem)
   */
  public void acceptProblem(/*@ non_null */ IProblem p) {
      // JML checking produces CompilerProblems (in OpenJMLInterface); 
      // Eclipse produces other kinds of problems;
      // Eclipse problems are already reported, so don't report them 
      // over again if JML encounters it as part of getting the Java AST.
      // Except: We swallow silently two errors - that a method requires a
      // body and uninitialized blank final fields, both of which occur in
      // specification files by design.
      if (!(p instanceof JmlEclipseProblem)) {
          int id = p.getID();
          if (!(id == IProblem.MethodRequiresBody || id == IProblem.UninitializedBlankFinalField)) return;
          String s = new String(p.getOriginatingFileName());
          if (s.endsWith(".java")) return;
          // FIXME - we are not actually doing anything.  SHould we?
          //          Log.log("JAVA Problem: " + id + " " + new String(p.getOriginatingFileName()) + " " + p.getMessage());
          //          p.delete();
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
              // No originating file name, so use the project or the workspace root
              f = project != null ? project : root;
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
          int severity = ((JmlEclipseProblem)p).severity;
          final boolean staticCheckWarning = 
              // The 64 is ProblemSeverities.SecondaryError, which has discouraged access
              severity == 64 || finalErrorMessage.contains("The prover") 
                              || finalErrorMessage.contains("Associated declaration");
          final int finalSeverity = 
              staticCheckWarning ? IMarker.SEVERITY_WARNING :
              p.isWarning() ? IMarker.SEVERITY_WARNING :
              severity > 0  ? IMarker.SEVERITY_ERROR :
                      IMarker.SEVERITY_INFO;

          // Eclipse recommends that things that modify the resources
          // in a workspace be performed in a IWorkspaceRunnable
          IWorkspaceRunnable runnable = new IWorkspaceRunnable() {
              public void run(IProgressMonitor monitor) throws CoreException {
                  IMarker marker = r.createMarker(
                          staticCheckWarning ? Utils.ESC_MARKER_ID : Utils.JML_MARKER_ID);
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
      } catch (Exception e) {
          Log.errorlog("Failed to make a marker " + e,e);
      }
      mostRecentProblem = p;
  }

  /** What to accept: level == 2 ==> errors only; level == 1; errors and
   * warnings
   */
  protected int level = 1;
  
  /** What to accept: level == 2 ==> errors only; level == 1; errors and
   * warnings
   * @param level whether to print warnings and info messages
   */
  public void setLevel(int level) {
    this.level = level;
  }
  
  /** This implementation does nothing in this call - all reported problems
   * are handled.
   * @see org.eclipse.jdt.core.IProblemRequestor#beginReporting()
   */
  public void beginReporting() {
    // do nothing
  }

  /** This implementation does nothing in this call - all reported problems
   * are handled.
   * @see org.eclipse.jdt.core.IProblemRequestor#endReporting()
   */
  public void endReporting() {
    // do nothing
  }

  /** This implementation is always active
   * @return always returns true
   * @see org.eclipse.jdt.core.IProblemRequestor#isActive()
   */
  public boolean isActive() {
    return true;
  }

}
