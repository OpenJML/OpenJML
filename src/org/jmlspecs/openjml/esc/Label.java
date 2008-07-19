package org.jmlspecs.openjml.esc;

/** This class defines labels used for identifying different kinds of assumptions
 * and assertions.  The human readable string may not have whitespace or any
 * non-alphanumeric characters (and must start with a letter).
 * @author David Cok
 *
 */
public class Label {

    /** Human-readable description of this kind of assertion or assumption */
    //@ non_null
    protected String info;
    
    /** Constructs a label object 
     * @param s name of label, alphanumeric only (no spaces)
     */
    protected Label(/*@ non_null */ String s) {
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
    public final static Label EXPLICIT_ASSUME = new Label("Assume");
    
    /** Used for basic assume statements generated from assignments */
    public final static Label ASSIGNMENT = new Label("Assignment");
    
    /** Used for assume statements generated from branches (then branch) */
    public final static Label BRANCHT = new Label("BranchThen");
    
    /** Used for assume statements generated from branches (else branch) */
    public final static Label BRANCHE = new Label("BranchElse");
    
    /** Used for assume statements generated from preconditions */
    public final static Label PRECONDITION = new Label("Precondition");
    
    /** Used for assume or assert statements generated from invariants */
    public final static Label INVARIANT = new Label("Invariant");
    
    /** Used for assume statements generated to define auxiliary variables */
    public final static Label SYN = new Label("Synthetic");

    /** Used for explicit, user-specified assert statements */
    public final static Label EXPLICIT_ASSERT = new Label("Assert");
    
    /** Used for asserts generated from user-specified unreachable statements */
    public final static Label UNREACHABLE = new Label("Unreachable");
    
    /** Used for assume or assert statements generated from non-null designations */
    public final static Label NULL_CHECK = new Label("NullCheck");
    
    /** Used for assert statements generated from postcondition checks */
    public final static Label POSTCONDITION = new Label("Postcondition");
    
    /** Used for assert statements generated from constraint checks */
    public final static Label CONSTRAINT = new Label("Constraint");
    
    /** Used for assert statements generated to check that assume statements are feasible */
    public final static Label ASSUME_CHECK = new Label("AssumeCheck");
    
    public final static Label LOOP_INVARIANT = new Label("LoopInvariant");
    
    public final static Label LOOP_DECREASES = new Label("LoopDecreases");
    public final static Label LOOP_DECREASES_NEGATIVE = new Label("LoopDecreasesNotPositive");
    
    public final static Label LOOP = new Label("LoopCondition");
}
