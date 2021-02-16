/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-20
 */
package org.jmlspecs.openjml.proverinterface;

/**
 * Thrown when something goes wrong in the communication
 * with the prover. It might die, or talk rubbish, or...
 *
 * @author rgrig 
 * @author reviewed/revised by David Cok
 */
public class ProverException extends Exception {

    /** Serializable ID */
    private static final long serialVersionUID = -3260524298115196815L;

    /** Possibly holds the most recent input, used for error messages */
    //@ nullable
    public String mostRecentInput = null;

    /**
     * Constructs a prover exception.
     * @param reason what went wrong
     */
    public ProverException(String reason) {
        super(reason);
    }

    /**
     * Constructs a prover exception.
     * @param reason what went wrong
     */
    public ProverException(Throwable reason) {
        super(reason);
    }

    /**
     * Constructs a prover exception.
     * @param reason what went wrong
     * @param rootReason what is the cause of the reason (sic!)
     */
    public ProverException(String reason, /*@ non_null */ Throwable rootReason) {
        super(reason, rootReason);
    }

}
