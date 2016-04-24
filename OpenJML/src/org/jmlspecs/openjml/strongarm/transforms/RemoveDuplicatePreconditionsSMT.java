package org.jmlspecs.openjml.strongarm.transforms;

import java.util.Set;

import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

public class RemoveDuplicatePreconditionsSMT extends RemoveDuplicatePreconditions {

    public static RemoveDuplicatePreconditionsSMT instance;

    public RemoveDuplicatePreconditionsSMT(Context context) {
        super(context);
    }
    
    public static void cache(Context context){
        if(instance==null){
            instance = new RemoveDuplicatePreconditionsSMT(context);
        }
    }
    /**
     * Here we translate down to SMT conditions to check if 
     * the preconditions in parent blocks imply the conditions in lower blocks.
     * 
     * We need to do this sort of thing in the case that simple rewriting isn't enough to dispatch 
     * duplicate precondtions. 
     */
    @Override
    public void filterBlock(JmlSpecificationCase block){
        
        // we keep repeating this 
        List<JmlMethodClause> replacedClauses = null;
        Set<String> filterSet = getFilterStrings();
        
        for(List<JmlMethodClause> clauses = block.clauses; clauses.nonEmpty(); clauses = clauses.tail){
            
            
            if(filterSet.contains(clauses.head.toString())==false){
                if(replacedClauses == null){
                    replacedClauses = List.of(clauses.head);
                }else{
                    replacedClauses = replacedClauses.append(clauses.head);
                }
            }
            
        }
        
        block.clauses = replacedClauses;
    }


}
