package org.jmlspecs.openjml.strongarm.transforms;

import java.util.Set;

import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.ext.MethodExprClauseExtensions;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.requiresClauseKind;
import static org.jmlspecs.openjml.ext.RecommendsClause.*;
import org.jmlspecs.openjml.strongarm.translators.SubstitutionEQProverSMT;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log.WriterKind;

public class RemoveDuplicatePreconditionsSMT extends RemoveDuplicatePreconditions {

    public static RemoveDuplicatePreconditionsSMT instance;
    private JmlMethodDecl currentMethod;

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
     * the preconditions in parent blocks imply the conditions 
     * in lower blocks.
     * 
     * We need to do this sort of thing in the case that simple 
     * rewriting isn't enough to dispatch duplicate precondtions. 
     */
    @Override
    public void filterBlock(JmlSpecificationCase block){
        
        // we keep repeating this 
        List<JmlMethodClause> replacedClauses = null;
        Set<JmlMethodClauseExpr> filterSet = getFilters();
        
        for(List<JmlMethodClause> clauses = block.clauses; clauses.nonEmpty(); clauses = clauses.tail){
            
            // Only include the preconditions not implied by previous preconditions
            // note that this is a path sensitive analysis -- the entire context of the current method's smt translation 
            // will be taken into account. For example, while a > 0 => a == 3 mahy not be generally true, it may be true
            // for the given method. A human would see this and not write it in the preconditions, thus we aim to 
            // filter this sort of thing out. 
            if(!(clauses.head instanceof JmlMethodClauseExpr) || clauses.head.clauseKind != requiresClauseKind || new SubstitutionEQProverSMT(context).checkImplies(filterSet, (JmlMethodClauseExpr)clauses.head, currentMethod)==false){
                if(replacedClauses == null){
                    replacedClauses = List.of(clauses.head);
                }else{
                    replacedClauses = replacedClauses.append(clauses.head);
                }
                
                if (verbose) {
                    log.getWriter(WriterKind.NOTICE).println("Kept EXPR: " + clauses.head);
                }
                
            }else{
                if (verbose) {
                    log.getWriter(WriterKind.NOTICE).println("Filtering EXPR: " + clauses.head);
                }
            }            
        }
        
        block.clauses = replacedClauses;
    }
    
    public static void simplify(JCTree node){
        instance.scan(node);
    }
    
    public static void simplify(JCTree node, JmlMethodDecl method){
        instance.currentMethod = method;
        RemoveDuplicatePreconditionsSMT.simplify(node);
    }
    
}
