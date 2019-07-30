package org.jmlspecs.openjml.strongarm.tree;

import java.util.Comparator;

import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.RecommendsClause.*;

public class ContractComparator implements Comparator<JmlMethodClause> {

    // ordering is requires, ensures, modifies (otherwise lexical)
    @Override
    public int compare(JmlMethodClause o1, JmlMethodClause o2) {
        
        if(o1.clauseKind == o2.clauseKind){
            return o1.toString().compareTo(o2.toString());
        }
        
        if(o1.clauseKind == requiresClauseKind && o2.clauseKind == ensuresClauseKind){
            return -1;
        }
        
        if(o2.clauseKind == requiresClauseKind && o1.clauseKind == ensuresClauseKind){
            return 1;
        }
        
        return o2.clauseKind.name().compareTo(o1.clauseKind.name());
    }
    
}