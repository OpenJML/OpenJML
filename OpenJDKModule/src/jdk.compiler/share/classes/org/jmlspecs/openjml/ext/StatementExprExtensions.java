package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.Extensions;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;

public class StatementExprExtensions extends JmlExtension {
    
    public static final String assertID = "assert";
    public static final String checkID = "check";
    public static final String assumeID = "assume";
    public static final String commentID = "comment";
    public static final String useID = "use";
    public static final String hencebyID = "hence_by";
    public static final String loopinvariantID = "loop_invariant";
    public static final String loopdecreasesID = "loop_decreases";
    
    public static final IJmlClauseKind assertClause = new StatementExprType(assertID);
    
    public static final IJmlClauseKind checkClause = new StatementExprType(checkID);
    
    public static final IJmlClauseKind assumeClause = new StatementExprType(assumeID);
    
    public static final IJmlClauseKind commentClause = new StatementExprType(commentID) ;
    
    public static final IJmlClauseKind useClause = new StatementExprType(useID);
    
    public static final IJmlClauseKind hencebyClause = new StatementExprType(hencebyID);
    
    public static final IJmlClauseKind loopinvariantClause = new StatementExprType(loopinvariantID);
    public static final IJmlClauseKind loopdecreasesClause = new StatementExprType(loopdecreasesID);
    
    @Override
    public void register() {
        synonym("decreases",loopdecreasesClause);
        synonym("decreasing",loopdecreasesClause);
        synonym("maintaining",loopinvariantClause);
    }
    
}
