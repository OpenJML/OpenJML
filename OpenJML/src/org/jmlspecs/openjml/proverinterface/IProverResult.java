/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.proverinterface;

import java.util.Collection;
import java.util.Date;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.annotation.NonNull;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.tree.JCTree;

public interface IProverResult {
    
    public static interface IFactory {
        public IProverResult makeProverResult(MethodSymbol msym, String prover, Kind kind, Date start);
    }

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
    static public final Kind POSSIBLY_SAT = new Kind("POSSIBLY_SAT");

    /** The logical assumptions were infeasible (and thus trivially satisfiable) */
    static public final Kind INFEASIBLE = new Kind("INFEASIBLE");

    /** The logical assertions were not satisfiable */
    static public final Kind UNSAT = new Kind("UNSAT");

    /** The result could not be determined (prover died, timed out, ...) */
    static public final Kind UNKNOWN = new Kind("UNKNOWN");

    /** The prover timed out */
    static public final Kind TIMEOUT = new Kind("TIMEOUT");

    /** The proof resulted in some internal error */
    static public final Kind ERROR = new Kind("ERROR");

    /** The proof was not attempted */
    static public final Kind SKIPPED = new Kind("SKIPPED");

    /** The proof is in progress */
    static public final Kind RUNNING = new Kind("RUNNING");

    /** The proof was cancelled before completion */
    static public final Kind CANCELLED = new Kind("CANCELLED");

    /** The proof was cancelled before completion */
    static public final Kind COMPLETED = new Kind("COMPLETED");

    /** Category of result produced by the prover */
    public Kind result();

    //@ model public Kind _result;
    
    /** Sets the category of result produced by the prover */
    //@ assignable _result;
    //@ ensures r == result();
    public void result(@NonNull Kind r);

    /** True if the prover was able to produce a satisfying assignment 
     * @return true if there is a satisfying assignment
     */
    //@ ensures \result == (result() == SAT || result() == POSSIBLY_SAT);
    public boolean isSat();

    /** A String identifying the kind of prover that was used
     * 
     * @return an identifying string for the kind of prover that was used
     */
    public String prover();
    
    /** The time to compute this result, in seconds */
    public double duration();
    
    public int episodes();

    /** The time at which the computation of the result began */
    public Date timestamp();

    /** The method for which this result was obtained */
    public Symbol.MethodSymbol methodSymbol();

    /** The satisfying assignment produced by the prover.
     * @return The satisfying assignment produced by the prover
     */
    //@ ensures result() != UNSAT ==> \result == null;
    //@ nullable
    public ICounterexample counterexample();

    //@ nullable pure
    public Object otherInfo();

    //@ ensures \result == this;
    public IProverResult setOtherInfo(Object s);

    /** Returns the set of core ids, or null if no such information is available 
     * @return an item holding the core id information
     */
    //@ ensures result() != SAT ==> \result == null;
    //@ nullable
    public ICoreIds coreIds();

    /** A marker interface for additional details produced by the prover -
     * these may be prover-dependent
     *
     */
    public static interface Item {}

    // TODO: Document
    public static class Span {
    	final static public int NORMAL = 0;
    	final static public int TRUE = 1;
    	final static public int FALSE = 2;
    	final static public int EXCEPTION = 3;
    	
        public int start;
        public int end;
        public int type; // Fake enum
        public Span(int start, int end, int type) { 
            this.start = start; this.end = end; this.type = type;
        }
        public String toString() { return "[" + start + ":" + end + " " + type + "]"; }
    }

    /** This interface describes a counterexample: a set of variable - value pairs 
     * that constitute a satisfying assignment for a given proof attempt.  
     * For flexibility, both variable and value are stored as Strings.
     * @author David Cok
     */
    public static interface ICounterexample extends Item {

//        /** Adds a variable - value pair to the counterexample 
//         * @param variable the String name of the variable
//         * @param value    the String representation of the value
//         */
//        public void put(String variable,String value);
//
//        /** Retrieves the String representation of the value for a given
//         * variable; returns null if none present in this counterexample.
//         * @param variable
//         * @return the corresponding value, in String form, or null if none available
//         */
//        public String get(String variable);
//
//        // TODO - needs more documentation
//        
//        public void put(JCTree expr,String value);
//        public void putMap(Map<String,String> map);
//        public Map<String,String> getMap();
        
        public String get(JCTree expr);

        public void putPath(List<Span> path);
        public List<Span> getPath();

        /** All of the variable-value pairs, returned as a Set of Map.Entry 
         * pairs, sorted alphabetically by variable name.
         * @return a sorted list of the variable-value pairs
         */
        public Set<Map.Entry<String,String>> sortedEntries();
    }

    /** An interface for a class holding core ids, expressed here as integers. */
    public static interface ICoreIds extends Item {
        public Collection<Integer> coreIds();
    }
}
