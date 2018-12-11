package org.jmlspecs.openjml.strongarm.tree;

import java.util.Comparator;

import org.jmlspecs.openjml.DefaultJmlTokenKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;

public class ContractComparator implements Comparator<JmlMethodClause> {

    // ordering is requires, ensures, modifies (otherwise lexical)
    @Override
    public int compare(JmlMethodClause o1, JmlMethodClause o2) {
        
        if(o1.token == o2.token){
            return o1.toString().compareTo(o2.toString());
        }
        
        if(o1.token == DefaultJmlTokenKind.REQUIRES && o2.token == DefaultJmlTokenKind.ENSURES){
            return -1;
        }
        
        if(o2.token == DefaultJmlTokenKind.REQUIRES && o1.token == DefaultJmlTokenKind.ENSURES){
            return 1;
        }
        
        return o2.token.toString().compareTo(o1.token.toString());
    }
    
}