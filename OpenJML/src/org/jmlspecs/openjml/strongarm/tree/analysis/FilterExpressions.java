package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.util.ArrayList;
import java.util.Set;

import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.strongarm.Strongarm;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

public class FilterExpressions extends JmlTreeAnalysis {
    
    private final Set<JmlMethodClause> filter;

    public FilterExpressions(Context context, Set<JmlMethodClause> filter) {
        super(context);
        
        this.filter = filter;
    }

    
    
    
    



    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase block) {

        List<JmlMethodClause> replacedClauses = null;
        
        if(block.clauses==null) return;
        
        for(List<JmlMethodClause> clauses = block.clauses; clauses.nonEmpty(); clauses = clauses.tail){
                        
            if(shouldRemove(clauses.head, clauses.tail) == false){
                if(replacedClauses == null){
                    replacedClauses = List.of(clauses.head);
                }else{
                    replacedClauses = replacedClauses.append(clauses.head);
                }
            }
        }
        
        block.clauses = replacedClauses;
        
        super.visitJmlSpecificationCase(block);
    }
    private boolean shouldRemove(JmlMethodClause head,
            List<JmlMethodClause> tail) {
        
        String clause = head.toString();
        
        boolean exists = filter.stream()
                .filter(x -> x.toString().equals(clause))
                .findFirst()
                .isPresent();
       
        
        return exists;
    }


    public static void analyze(JCTree tree, Set<JmlMethodClause> intersection) {

        FilterExpressions analysis = new FilterExpressions(
                Strongarm._context, intersection);
        analysis.doAnalysis(tree);
    }


    private void doAnalysis(JCTree tree) {
        scan(tree);
        
    }
}
