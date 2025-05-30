/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

/**
 * Instances of this exception class are thrown to indicate that processing
 * should be aborted, but it is a nuisance to try to cleanly exit from down
 * in the call stack, so an instance of this class, perhaps wrapped in a
 * PropagatedException, as used. 
 * Any relevant error messages should be emitted before throwing the exception.
 * 
 * @author David Cok
 */
public class JmlInternalAbort extends RuntimeException {

    /**
     * Version control for this Serializable class.
     */
    private static final long serialVersionUID = 2146006306510130632L;

    /**
     * Constructs an instance.
     * You should have already logged an error message with as much other
     * information as you can.
     */
    public JmlInternalAbort() {
    }
    
    /**
     * Constructs an instance containing error information.
     */
    public JmlInternalAbort(String message) {
        super(message);
    }
    
    public String toString() {
        //Utils.dumpStack("JmlInternalAbort");
        return super.toString();
    }
}
