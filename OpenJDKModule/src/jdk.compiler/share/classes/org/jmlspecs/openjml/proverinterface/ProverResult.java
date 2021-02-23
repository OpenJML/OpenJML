/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.proverinterface;

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
	/*@nullable*/ /*@spec_public*/
    public Kind result;

    /** Descriptor of the prover used */
	/*@nullable*/ /*@spec_public*/
    protected String prover;
    
    /** Time taken ( in secs) to compute this proof result */
    protected double duration;
    
    protected int episodes; // Number of different solver attempts that contributed to the duration
    
    /** Time at which the proof attempt started */
    /*@non_null*/
    protected Date timestamp;
    
    /** The Method symbol of the target method of this proof attempt */
    /*@non_null*/
    public MethodSymbol methodSymbol;
    
    /** Other information - user defined */
    /*@nullable*/
    protected Object otherInfo;
    
    /** The details of the result produced by the prover, if any */
    /*@nullable*/
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
    /*@pure*/
    public Kind result() { return result; }

    /** Returns a descriptor of the prover used to generate the result
     * @return a descriptor of the prover
     */
    /*@pure*/ /*@nullable*/
    public String prover() { return prover; }
    
    /** The time to compute this result, in seconds */
    public double duration() { return duration; }
    
    public int episodes() { return episodes; }

    /** Sets the time to compute this result */
    public void accumulateDuration(double d) { duration += d; episodes++; }
    
    /** The method that was the target of this proof attempt */
    /*@non_null*/
    public MethodSymbol methodSymbol() { return methodSymbol; }
    
    /** The time at which the computation of the result began */
    /*@non_null*/
    public Date timestamp() { return timestamp; }

    /** Sets the time at which the computation of the result began */
    public void setTimestamp(Date d) { timestamp = d; }
    
    /** Returns the associated information object */
    /*@pure*/ /*@nullable*/
    public Object otherInfo() { return otherInfo; }
    
    /** Sets the associated information object. */
    //@ assignable otherInfo;
    //@ ensures o == otherInfo();
    public ProverResult setOtherInfo(/*@nullable*/ Object o) {
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
    public void result(/*@non_null*/ Kind r) { result = r; }

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
    /*@non_null*/ public List<IProverResult.Item> details() {
        return details;
    }

    /** Adds an item to the list of details
     * 
     * @param item the detail item to add
     */
    public void add(IProverResult./*@non_null*/ Item item) {
        if (details == null) details = new LinkedList<IProverResult.Item>();
        details.add(item);
    }

    /** Returns the counterexample information, if any available and if the
     * prover supports it
     */
    /*@nullable*/
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
    /*@nullable*/
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
