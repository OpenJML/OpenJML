/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

/**
 * Instances of this exception class are thrown to indicate catastrophic fatal
 * errors in the OpenJML tool. These are unexpected situations, probably
 * indicating a bug, that cannot be or are not worth trying to recover from.
 * Don't worry about any exception messages from this class - it is simply a
 * marker. Log any error messages before constructing an instance.
 * 
 * @author David Cok
 */
public class JmlInternalException extends RuntimeException {

    /**
     * Version control for this Serializable class.
     */
    private static final long serialVersionUID = 2146006306510130631L;

    /**
     * Constructs an instance, printing the current stack trace to System.err.
     * You should have already logged an error message with as much other
     * information as you can.
     */
    public JmlInternalException() {
        this.printStackTrace(System.err);
    }
    
    /**
     * Constructs an instance, printing the current stack trace to System.err.
     * You should have already logged an error message with as much other
     * information as you can.
     */
    public JmlInternalException(String msg) {
        super(msg);
        System.err.println(msg);
        this.printStackTrace(System.err);
    }
}
