/**
 * Copyright (c) 2005 David R. Cok
 * @author David R. Cok
 * Created Jul 9, 2005
 */
package org.jmlspecs.openjml.eclipse;

import java.util.Map;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IProblemRequestor;
import org.eclipse.jdt.core.compiler.IProblem;

// TODO - this tool reports problems by directly calling an instance
// of this IProblemRequestor.  The Eclipse framework actually uses
// a combination of a ProblemReporter to which problems are reported
// and requestors that can subscribe to problem reports.  Perhaps we
// should correct to that model.

/**
 * This is a partial implementation of the IProblemRequestor
 * interface as used in this application.  It adds one bit of
 * functionality - the ability to provide a mapping from 
 * IFile paths to working copies so that the right source text 
 * can be associated with a given problem message without having
 * to be sure that potential changes are written to disk.
 */
abstract public class JmlProblemRequestor implements IProblemRequestor {
  
  /**
   * This is a map of filename to compilation unit.
   * The filename is gotten from IResource.getFullPath().toString().  
   * The compilation unit is typically a working copy, not necessarily 
   * saved to disk. Its text information can be obtained from 
   * getSource() after reconciliation.
   */
  private Map<String,ICompilationUnit> map = null;
  
  /** Sets the map of filenames to compilation units
   * @param map the new map
   */  // FIXME - is setMap, or the map itself, actually used anywhere
  public void setMap(Map<String,ICompilationUnit> map) {
    this.map = map;
  }
  
  /**
   * Returns the ICompilationUnit corresponding to the given path,
   * or null if none found
   * @param p the path used as a key
   * @return the associated ICompilationUnit
   */
  public ICompilationUnit getICU(String p) {
    return map == null ? null : map.get(p);
  }

  /* (non-Javadoc)
   * @see org.eclipse.jdt.core.IProblemRequestor#acceptProblem(org.eclipse.jdt.core.compiler.IProblem)
   */
  abstract public void acceptProblem(IProblem problem);

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
  
  /* (non-Javadoc)
   * @see org.eclipse.jdt.core.IProblemRequestor#beginReporting()
   */
  public void beginReporting() {
    // do nothing
  }

  /* (non-Javadoc)
   * @see org.eclipse.jdt.core.IProblemRequestor#endReporting()
   */
  public void endReporting() {
    // do nothing
  }

  /* (non-Javadoc)
   * @see org.eclipse.jdt.core.IProblemRequestor#isActive()
   */
  public boolean isActive() {
    return true;
  }

}
