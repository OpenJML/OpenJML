package org.jmlspecs.openjml.proverinterface;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

public interface IProverResult {

  /** Kinds of results a prover can produce */
  static public final class Kind {
      final private /*@non_null*/String string;
      private Kind(/*@non_null*/String s) { string = s; }
      public String toString() { return string; }
  }
  
  /** The logical assertions were satisfiable */
  static public final Kind SAT = new Kind("SAT");
  
  /** The logical assertions were satisfiable, but since the logic engine
   * is incomplete, the counterexample may actually be spurious */
  static public final Kind POSSIBLYSAT = new Kind("POSSIBLYSAT");
  
  /** The logical assertions were not satisfiable */
  static public final Kind UNSAT = new Kind("UNSAT");
  
  /** The result could not be determined (prover died, timed out, ...) */
  static public final Kind UNKNOWN = new Kind("UNKNOWN");
  
  /** Category of result produced by the prover */
  public Kind result();
  
  /** True if the prover was able to produce a satisfying assignment 
   * @return true if there is a satisfying assignment
   */
  //@ ensures \result == (result() == SAT || result() == POSSIBLY_SAT);
  public boolean isSat();
  
  /** The satisfying assignment produced by the prover.
   * @return The satisfying assignment produced by the prover
   */
  //@ ensures result() != UNSAT ==> \result == null;
  public ICounterexample counterexample();
  
  /** Returns the set of core ids, or null if no such information is available 
   * @return an item holding the core id information
   */
  //@ ensures result() != SAT ==> \result == null;
  public ICoreIds coreIds();
  
  /** A marker interface for additional details produced by the prover -
   * these may be prover-dependent
   *
   */
  public static interface Item {}
  
  /** This interface describes a counterexample: a set of variable - value pairs 
   * that constitute a counterexample for a given proof attempt.  
   * For flexibility, both variable and value are stored as Strings.
   * @author David Cok
   */
  public static interface ICounterexample extends Item {
      
      /** Adds a variable - value pair to the counterexample 
        * @param variable the String name of the variable
        * @param value    the String representation of the value
        */
      public void put(String variable,String value);
      
      /** Retrieves the String representation of the value for a given
       * variable; returns null if none present in this counterexample.
       * @param variable
       * @return the corresponding value, in String form, or null if none available
       */
      public String get(String variable);
      
      /** All of the variable-value pairs, returned as a Set of Map.Entry 
       * pairs, sorted alphabetically by variable name.
       * @return
       */
      public Set<Map.Entry<String,String>> sortedEntries();
  }
  
  /** An interface for a class holding core ids, expressed here as integers. */
  public static interface ICoreIds extends Item {
      public Collection<Integer> coreIds();
  }
}
