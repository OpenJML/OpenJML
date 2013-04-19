/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.proverinterface;

import org.jmlspecs.annotation.*;

import java.util.LinkedList;
import java.util.List;

/** This class is a concrete representation of an IProverResult
 * 
 * @author David Cok
 */
public class ProverResult implements IProverResult {

    /** The result obtained on testing a logical assertion */
    @Nullable @SpecPublic
    protected Kind result;

    /** Descriptor of the prover used */
    @Nullable @SpecPublic
    protected String prover;
    
    /** Other information - user defined */
    @Nullable
    protected Object otherInfo;
    
    /** The details of the result produced by the prover, if any */
    @Nullable
    protected List<IProverResult.Item> details = null;

    /** Creates a mostly empty ProverResult object, with the prover
     * description initialized.
     * @param prover A description of the prover used
     */
    //@ assignable this.prover;
    //@ ensures prover == this.prover();
    public ProverResult(String prover) {
        this.prover = prover;
    }
    
    /** Creates a mostly empty ProverResult object, with the prover
     * description and basic result initialized.
     * @param prover A description of the prover used
     */
    public ProverResult(String prover, Kind result) {
        this.prover = prover;
        this.result = result;
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
    
    /** Returns the associated information object */
    @Pure @Nullable
    public Object otherInfo() { return otherInfo; }
    
    /** Sets the associated information object. */
    //@ assignable otherInfo;
    //@ ensures o == otherInfo();
    public void setOtherInfo(@Nullable Object o) {
        otherInfo = o;
    }
    
    /** Sets the result category
     * @param r the value of the result category
     */
    //@ also
    //@ assignable this.result;
    //@ ensures result() == r;
    //JAVA16 @Override
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
    
    /** Informational string */
    public String toString() {
        return result() + " [" + prover() + "]";
    }
}
