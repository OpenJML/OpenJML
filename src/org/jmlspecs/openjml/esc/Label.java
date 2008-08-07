package org.jmlspecs.openjml.esc;

/** This class defines labels used for identifying different kinds of assumptions
 * and assertions.  The human readable string may not have whitespace or any
 * non-alphanumeric characters (and must start with a letter).
 * <P>
 * This could be implemented with an enum, but that is not extendable by 
 * derived classes.  So instead we use a set of final objects of type Label.
 * Others can be easily created if needed.
 * 
 * @author David Cok
 */
public class Label {

    /** Human-readable description of this kind of assertion or assumption */
    //@ non_null
    protected final String info;
    
    /** Constructs a label object 
     * @param s name of label, alphanumeric only (no spaces)
     */
    public Label(/*@ non_null */ String s) {
        this.info = s;
    }
    
    /** Returns the info String for this instance
      * @see java.lang.Object#toString()
     */
    //@ non_null
    public String toString() {
        return info;
    }
    
    /** Used for explicit, user-provided JML assume statements */
    /*@ non_null*/ public final static Label EXPLICIT_ASSUME = new Label("Assume");
    
    /** Used for basic assume statements generated from assignments */
    /*@ non_null*/ public final static Label ASSIGNMENT = new Label("Assignment");
    
    /** Used for basic assume statements generated from top-level block equations */
    /*@ non_null*/ public final static Label BLOCKEQ = new Label("BlockEquation");
    
    /** Used for assume statements generated from branches (then branch) */
    /*@ non_null*/ public final static Label BRANCHT = new Label("BranchThen");
    
    /** Used for assume statements generated from branches (else branch) */
    /*@ non_null*/ public final static Label BRANCHE = new Label("BranchElse");
    
    /** Used for assume statements generated from preconditions */
    /*@ non_null*/ public final static Label PRECONDITION = new Label("Precondition");
    
    /** Used for assume or assert statements generated from invariants */
    /*@ non_null*/ public final static Label INVARIANT = new Label("Invariant");
    
    /** Used for assume statements generated to guard a catch block */
    /*@ non_null*/ public final static Label CATCH_CONDITION = new Label("CatchCondition");

    /** Used for assume statements generated to define auxiliary variables */
    /*@ non_null*/ public final static Label SYN = new Label("Synthetic");

    /** Used for explicit, user-specified assert statements */
    /*@ non_null*/ public final static Label EXPLICIT_ASSERT = new Label("Assert");
    
    /** Used for asserts generated from user-specified unreachable statements */
    /*@ non_null*/ public final static Label UNREACHABLE = new Label("Unreachable");
    
    /** Used for assume or assert statements generated from non-null designations */
    /*@ non_null*/ public final static Label NULL_CHECK = new Label("NullCheck");
    
    /** Used for assert statements generated from postcondition checks */
    /*@ non_null*/ public final static Label POSTCONDITION = new Label("Postcondition");
    
    /** Used for assert statements generated from exceptional postcondition checks */
    /*@ non_null*/ public final static Label SIGNALS = new Label("ExceptionalPostcondition");
    
    /** Used for assert statements generated from signals_only checks */
    /*@ non_null*/ public final static Label SIGNALS_ONLY = new Label("ExceptionList");
    
    /** Used for assume statements generated from uses of pure methods in specifications */
    /*@ non_null*/ public final static Label METHODAXIOM = new Label("MethodAxiom");
    
    /** Used for assert statements generated from constraint checks */
    /*@ non_null*/ public final static Label CONSTRAINT = new Label("Constraint");
    
    /** Used for assert statements generated from initially checks */
    /*@ non_null*/ public final static Label INITIALLY = new Label("Initially");
    
    /** Used for assert statements generated to check that assume statements are feasible */
    /*@ non_null*/ public final static Label ASSUME_CHECK = new Label("AssumeCheck");
    
    /** Used for the loop invariant assertion or assumption. */
    /*@ non_null*/ public final static Label LOOP_INVARIANT = new Label("LoopInvariant");
    
    /** Used for the assertion that the loop variant is decreasing. */
    /*@ non_null*/ public final static Label LOOP_DECREASES = new Label("LoopDecreases");
    
    /** Used for the assertion that the loop variant is never negative prior to executing a loop iteration. */
    /*@ non_null*/ public final static Label LOOP_DECREASES_NEGATIVE = new Label("LoopDecreasesNotPositive");
    
    /** Used to designate the conditional test of a loop */
    /*@ non_null*/ public final static Label LOOP = new Label("LoopCondition");
    
    /** Used to designate an undefined pure expression because of a potential null reference */
    /*@ non_null*/ public final static Label UNDEFINED_NULL = new Label("UndefinedNullReference");
    
    /** Used to designate an undefined pure expression because of a potential negative index */
    /*@ non_null*/ public final static Label UNDEFINED_NEGATIVEINDEX = new Label("UndefinedNegativeIndex");
    
    /** Used to designate an undefined pure expression because of a potential too-large index */
    /*@ non_null*/ public final static Label UNDEFINED_TOOLARGEINDEX = new Label("UndefinedTooLargeIndex");
    
    /** Used to designate an undefined pure expression because of a potential divide by 0 */
    /*@ non_null*/ public final static Label UNDEFINED_DIV0 = new Label("UndefinedDivideByZero");
    
    /** Used to designate an undefined pure expression because of a potential bad cast */
    /*@ non_null*/ public final static Label UNDEFINED_CAST = new Label("UndefinedBadCast");
    
    /** Used to designate an undefined pure expression because of a failed precondition in a called method */
    /*@ non_null*/ public final static Label UNDEFINED_PRECONDITION = new Label("UndefinedCalledMethodPrecondition");
    
    
    /** Used to designate a possible exception because of a potential null reference */
    /*@ non_null*/ public final static Label POSSIBLY_NULL = new Label("PossiblyNullReference");
    
    /** Used to designate a possible exception because of a potential negative index */
    /*@ non_null*/ public final static Label POSSIBLY_NEGATIVEINDEX = new Label("PossiblyNegativeIndex");
    
    /** Used to designate a possible exception because of a potential too-large index */
    /*@ non_null*/ public final static Label POSSIBLY_TOOLARGEINDEX = new Label("PossiblyTooLargeIndex");
    
    /** Used to designate a possible exception because of a potential divide by 0 */
    /*@ non_null*/ public final static Label POSSIBLY_DIV0 = new Label("PossiblyDivideByZero");

    /** Used to designate a possible exception because of a bad cast */
    /*@ non_null*/ public final static Label POSSIBLY_CAST = new Label("PossiblyBadCast");
    

}
