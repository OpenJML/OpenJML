package org.jmlspecs.openjml.strongarm.tree;

import java.util.Comparator;

import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;

public class ContractComparator implements Comparator<JmlMethodClause> {

    // ordering is requires, ensures, modifies (otherwise lexical)
    @Override
    public int compare(JmlMethodClause o1, JmlMethodClause o2) {
        
        if(o1.clauseType == o2.clauseType){
            return o1.toString().compareTo(o2.toString());
        }
        
        if(o1.clauseType == requiresClause && o2.clauseType == ensuresClause){
            return -1;
        }
        
        if(o2.clauseType == requiresClause && o1.clauseType == ensuresClause){
            return 1;
        }
        
        return o2.clauseType.name().compareTo(o1.clauseType.name());
    }
    
}