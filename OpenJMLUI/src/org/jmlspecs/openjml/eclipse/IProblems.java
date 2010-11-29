/*
 * Copyright (c) 2005-2010 David R. Cok
 * @author David R. Cok
 * Created Aug 19, 2005
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jdt.internal.compiler.problem.ProblemSeverities;

/**
 * An interface for the objects used within the UI to describe problems.
 */
public interface IProblems {
  /** Returns the unique identifier of the message
   * @return The unique identifier of the message
   */
  public int id();

  /**
   * A template in java.text.MessageFormat style
   */
  public String toString();

  /** Returns the severity of the problem
   * @return The severity of the problem
   */
  public int severity();
  
  // We make copies of the ProblemSeverities constants here because they are
  // not technically public.
  
  /** A severity value indicating an illegal or unrecoverable situation */
  public static final int ERROR = ProblemSeverities.Error;
  /** A severity level indicating a potential but not illegal problem */
  public static final int WARN = ProblemSeverities.Warning;
  /** A severity level indicating that a condition should be ignored (and any message suppressed) */
  public static final int IGNORE = ProblemSeverities.Ignore;
  
  /**
   * Returns the message consisting of the template with the arguments
   * substituted.
   * @param messageArgs The arguments to substitute in the template
   * @return The resulting String
   */
  public String toString(Object... messageArgs);
}

