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
    
    public final static Label EXPLICIT_ASSUME = new Label("Assume");
    public final static Label ASSIGNMENT = new Label("Assignment");
    public final static Label BRANCHT = new Label("BranchThen");
    public final static Label BRANCHE = new Label("BranchElse");
    public final static Label PRECONDITION = new Label("Precondition");
    public final static Label INVARIANT = new Label("Invariant");
    public final static Label SYN = new Label("Synthetic");

    public final static Label EXPLICIT_ASSERT = new Label("Assert");
    public final static Label UNREACHABLE = new Label("Unreachable");
    public final static Label NULL_CHECK = new Label("NullCheck");
    public final static Label POSTCONDITION = new Label("Postcondition");
    public final static Label CONSTRAINT = new Label("Constraint");
    public final static Label ASSUME_CHECK = new Label("AssumeCheck");
}
