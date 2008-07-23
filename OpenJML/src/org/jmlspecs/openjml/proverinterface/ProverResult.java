package org.jmlspecs.openjml.proverinterface;

import org.jmlspecs.annotations.*;

import java.util.LinkedList;
import java.util.List;

/** This class is a concrete representation of an IProverResult
 * 
 * @author David Cok
 */
public class ProverResult implements IProverResult {

    /** The result obtained on testing a logical assertion */
    @Nullable
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
    
    /** The details of the result 
     * @return a list of Item objects giving more detail
     */
    @NonNull public List<IProverResult.Item> details() {
        return details;
    }

    /** Adds an item to the list of details
     * 
     * @param item the detail item to add
     */
    public void add(@NonNull IProverResult.Item item) {
        if (details == null) details = new LinkedList<IProverResult.Item>();
        details.add(item);
    }

    /** Returns the counterexample information, if any available and if the
     * prover supports it
     */
    public Counterexample counterexample() {
        if (details == null) return null;
        for (IProverResult.Item i: details) {
            if (i instanceof Counterexample) {
                return (Counterexample)i;
            }
        }
        return null;
    }

    /** Returns any core id information, if available and supported by the
     * prover
     * @return an object holding the core id information
     */
    public ICoreIds coreIds() {
        if (details == null) return null;
        for (IProverResult.Item i: details) {
            if (i instanceof ICoreIds) {
                return (ICoreIds)i;
            }
        }
        return null;
    }
}
