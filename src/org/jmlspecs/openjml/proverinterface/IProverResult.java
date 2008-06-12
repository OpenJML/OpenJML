package org.jmlspecs.openjml.proverinterface;

public interface IProverResult {

  /** Kinds of results a prover can produce */
  static public final class Kind {}
  
  /** The logical assertions were satisfiable */
  static public final Kind SAT = new Kind();
  
  /** The logical assertions were not satisfiable */
  static public final Kind UNSAT = new Kind();
  
  /** The result could not be determined (prover died, timed out, ...) */
  static public final Kind UNKNOWN = new Kind();
  
  /** Category of result produced by the prover */
  public Kind result();
  
  /** True if the prover was able to produce a satisfying assignment 
   * @return true if there is a satisfying assignment
   */
  public boolean isSat();
  
  /** The satisfying assignment produced by the prover; currently, the
   * form of this output string is prover-dependent (FIXME)
   * @return The satisfying assignment produced by the prover
   */
  public String counterexample();
  
  /** A marker interface for additional details produced by the prover -
   * these may be prover-dependent
   *
   */
  public static interface Item {}
}
