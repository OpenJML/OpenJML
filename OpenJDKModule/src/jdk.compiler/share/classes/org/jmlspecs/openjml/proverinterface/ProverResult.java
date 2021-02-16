/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.proverinterface;

import org.jmlspecs.annotation.*;

import com.sun.tools.javac.code.Symbol.MethodSymbol;

import java.util.Date;
import java.util.LinkedList;
import java.util.List;

/** This class is a concrete representation of an IProverResult
 * 
 * @author David Cok
 */
public class ProverResult implements IProverResult {

    /** The result obtained on testing a logical assertion */
    @Nullable @SpecPublic
    public Kind result;

    /** Descriptor of the prover used */
    @Nullable @SpecPublic
    protected String prover;
    
    /** Time taken ( in secs) to compute this proof result */
    protected double duration;
    
    protected int episodes; // Number of different solver attempts that contributed to the duration
    
    /** Time at which the proof attempt started */
    @NonNull
    protected Date timestamp;
    
    /** The Method symbol of the target method of this proof attempt */
    @NonNull
    public MethodSymbol methodSymbol;
    
    /** Other information - user defined */
    @Nullable
    protected Object otherInfo;
    
    /** The details of the result produced by the prover, if any */
    @Nullable
    protected List<IProverResult.Item> details = null;

    /** Creates a mostly empty ProverResult object, with the prover
     * description and basic result initialized.
     * @param prover A description of the prover used
     */
    public ProverResult(String prover, Kind result, MethodSymbol msym) {
        this.prover = prover;
        this.timestamp = new Date(); // current time
        this.result = result;
        this.methodSymbol = msym;
    }

    /** Returns the category of result that the prover obtained
     * @return the category of result from the prover
     */
    @Pure
    public Kind result() { return result; }

    /** Returns a descriptor of the prover used to generate the result
     * @return a descriptor of the prover
     */
    @Pure
    public @Nullable String prover() { return prover; }
    
    /** The time to compute this result, in seconds */
    public double duration() { return duration; }
    
    public int episodes() { return episodes; }

    /** Sets the time to compute this result */
    public void accumulateDuration(double d) { duration += d; episodes++; }
    
    /** The method that was the target of this proof attempt */
    @NonNull
    public MethodSymbol methodSymbol() { return methodSymbol; }
    
    /** The time at which the computation of the result began */
    @NonNull
    public Date timestamp() { return timestamp; }

    /** Sets the time at which the computation of the result began */
    public void setTimestamp(Date d) { timestamp = d; }
    
    /** Returns the associated information object */
    @Pure @Nullable
    public Object otherInfo() { return otherInfo; }
    
    /** Sets the associated information object. */
    //@ assignable otherInfo;
    //@ ensures o == otherInfo();
    public ProverResult setOtherInfo(@Nullable Object o) {
        otherInfo = o;
        return this;
    }
    
    /** Sets the result category
     * @param r the value of the result category
     */
    //@ also
    //@ assignable this.result;
    //@ ensures result() == r;
    @Override
    public void result(@NonNull Kind r) { result = r; }

    /** Returns true if the prover found a satisfying assignment 
     * @return true if the prover found a satisfying assignment
     */
    //@ ensures \result == (result() == SAT);
    public boolean isSat() {
        return result == SAT || result == POSSIBLY_SAT;
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
    public void add(IProverResult.@NonNull Item item) {
        if (details == null) details = new LinkedList<IProverResult.Item>();
        details.add(item);
    }

    /** Returns the counterexample information, if any available and if the
     * prover supports it
     */
    @Nullable
    public ICounterexample counterexample() {
        if (details == null) return null;
        for (IProverResult.Item i: details) {
            if (i instanceof ICounterexample) {
                return (ICounterexample)i;
            }
        }
        return null;
    }

    /** Returns any core id information, if available and supported by the
     * prover
     * @return an object holding the core id information
     */
    @Nullable
    public ICoreIds coreIds() {
        if (details == null) return null;
        for (IProverResult.Item i: details) {
            if (i instanceof ICoreIds) {
                return (ICoreIds)i;
            }
        }
        return null;
    }
    
    /** Informational string */
    public String toString() {
        return result() + " [" + prover() + "]";
    }
}
