/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

/**
 * Instances of this exception class are thrown to indicate that processing
 * should be aborted, but any relevant messages have already been posted.
 * 
 * @author David Cok
 */
public class JmlInternalAbort extends RuntimeException {

    /**
     * Version control for this Serializable class.
     */
    private static final long serialVersionUID = 2146006306510130632L;

    /**
     * Constructs an instance, printing the current stack trace to System.err.
     * You should have already logged an error message with as much other
     * information as you can.
     */
    public JmlInternalAbort() {
    }
}
