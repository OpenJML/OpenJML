package org.jmlspecs.openjml;

public abstract class IJmlClauseType {

    abstract public String name();
    
    public String toString() { return name(); }
    
    /** If true, is a method or type spec clause types in which \old without a label can be used
    */
    public boolean oldNoLabelAllowed() { return false; }
    
    /** If true, is a clause in which \pre and \old with a label can be used (e.g. asst)
     */
    public boolean preOrOldWithLabelAllowed() { return false; }
    
    /** If true, is a method clause type in which these tokens may appear:
     *  \not_assigned \only_assigned \only_captured \only_accessible \not_modified */
    public boolean postClauseAllowed() { return false; }
    
    /** If true, is a method clause type in which the \result token may appear 
     * (and \not_assigned \only_assigned \only_captured \only_accessible \not_modified) */
    public boolean resultExpressionAllowed() { return false; }

    /** If true, is a method clause type in which the \exception token may appear 
     */
    public boolean exceptionExpressionAllowed() { return false; }

    /** If true, is a method clause type in which the \fresh token may appear 
     */
    public boolean freshExpressionAllowed() { return false; }

}
