package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlExtension;

public class StatementExprExtensions implements JmlExtension.MethodClause {
    
    public static final String assertID = "assert";
    public static final String assumeID = "assume";
    public static final String commentID = "comment";
    public static final String useID = "use";
    public static final String hencebyID = "henceby";
    public static final String loopinvariantID = "loop_invariant";
    public static final String loopdecreasesID = "loop_decreases";
    
    public static final IJmlClauseType assertClause = new StatementExprType(assertID);
    
    public static final IJmlClauseType assumeClause = new StatementExprType(assumeID);
    
    public static final IJmlClauseType commentClause = new StatementExprType(commentID) ;
    
    public static final IJmlClauseType useClause = new StatementExprType(useID);
    
    public static final IJmlClauseType hencebyClause = new StatementExprType(hencebyID);
    
    public static final IJmlClauseType loopinvariantClause = new StatementExprType(loopinvariantID);
    public static final IJmlClauseType loopdecreasesClause = new StatementExprType(loopdecreasesID);
    
    @Override
    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            assertClause, assumeClause, useClause, commentClause, hencebyClause,
            loopinvariantClause, loopdecreasesClause }; }
    
}
