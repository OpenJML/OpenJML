package org.jmlspecs.openjml.proverinterface;

import org.jmlspecs.annotations.*;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ProverResult implements IProverResult {

    /** The result obtained on testing a logical assertion */
    protected Kind result;

    /** The details of the result produced by the prover, if any */
    @Nullable
    protected List<IProverResult.Item> details = null;

    /** Returns the category of result that the prover obtained
     * @return the category of result from the prover
     */
    @Pure
    public Kind result() { return result; }

    /** Sets the result category
     * @param r the value of the result category
     */
    //@ ensures result() == r;
    public void result(@NonNull Kind r) { result = r; }

    /** Returns true if the prover found a satisfying assignment 
     * @return true if the prover found a satisfying assignment
     */
    //@ ensures \result == (result() == SAT);
    public boolean isSat() {
        return result == SAT;
    }
    
    // TODO - review/revise the rest

    /** The details of the result */
    public List<IProverResult.Item> details() {
        return details;
    }

    public void add(IProverResult.Item o) {
        if (details == null) details = new LinkedList<IProverResult.Item>();
        details.add(o);
    }

//    public static class Counterexample implements IProverResult.Item {
//        public Counterexample(String s) { counterexample = s; }
//        public String counterexample;
//        public String toString() { return counterexample; }
//    }

    public Counterexample counterexample() {
        if (details == null) return null;
        for (IProverResult.Item i: details) {
            if (i instanceof Counterexample) {
                return (Counterexample)i;
            }
        }
        return null;
    }

}
