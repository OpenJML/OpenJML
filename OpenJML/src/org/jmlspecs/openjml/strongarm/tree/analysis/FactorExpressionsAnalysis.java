package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.strongarm.Strongarm;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log.WriterKind;

public class FactorExpressionsAnalysis extends JmlTreeAnalysis {

    public FactorExpressionsAnalysis(Context context) {
        super(context);
    }

    private ArrayList<JmlMethodClauseGroup> path = new ArrayList<JmlMethodClauseGroup>();
    private Map<JmlMethodClauseGroup, Set<JmlMethodClauseExpr>> joins = new HashMap<JmlMethodClauseGroup, Set<JmlMethodClauseExpr>>();
    
    private ArrayList<JmlMethodClauseGroup> reverseGraph(){
        
        ArrayList<JmlMethodClauseGroup> r = new ArrayList<JmlMethodClauseGroup>(path);
        
        Collections.reverse(r);
        
        return r;
    }

    private void printIntersectionMap(){
        
        if(verbose){
        
            for(JmlMethodClauseGroup k : joins.keySet()){
                
                log.getWriter(WriterKind.NOTICE).println(">Group Start<");

                log.getWriter(WriterKind.NOTICE).println(k.toString());

                log.getWriter(WriterKind.NOTICE).println("Intersections:");
                
                for(JmlMethodClauseExpr e : joins.get(k)){
                    log.getWriter(WriterKind.NOTICE).println("\t -> " + e.toString());
                }

                log.getWriter(WriterKind.NOTICE).println(">Group End<");

            }
            
        }
    }

    private void doAnalysis(JCTree tree){
        // step 1
        // find the reverse graph
        scan(tree);
        
        ArrayList<JmlMethodClauseGroup> R = reverseGraph();
        
        // step 2
        // next, for each join (OR), find the intersection of the sets of propositions. 
        // for each join point, we require that (if it's not a block of statements) that 
        // the join point has been previously computed. 
                
        Map<JmlMethodClauseGroup, Set<JmlMethodClauseExpr>> blockMap = new HashMap<JmlMethodClauseGroup, Set<JmlMethodClauseExpr>>();
        
        while(R.size() > 0){ // fixpoint 
            for (Iterator<JmlMethodClauseGroup> iterator = R.iterator(); iterator.hasNext();) {
                
                JmlMethodClauseGroup G = iterator.next();
                
                Set<JmlMethodClauseExpr> intersection = getIntersection(G);
                
                if(intersection!=null){
                    joins.put(G, intersection);
                    iterator.remove();
                }
                
                
            }
        }

        printIntersectionMap();
        
        // step 3 "bubbling"
        // at this point, we should have computed all of the intersections. 
        // we could stop here and have a slightly reduced contract; however, to maximize 
        // the reduction in the size of the contract, we "bubble" up things in the intersection 
        // that exist in the intersection of a child clause, but not necessarily in the parent. 
        // of course, it is possible that contradictory statements could be in the group we are trying 
        // to bubble to that contradict the clause we are bubbling. to prevent this, we make sure there 
        // are no conflicts prior to adding it to the intersections.
        
        
        
    }

    private Set<JmlMethodClauseExpr> getIntersection(JmlMethodClauseGroup tree) {

        // the precondition for getting the intersection is that either 
        // a) ALL parts of the group are lists of expressions
        // or 
        // b) We have computed an intersection for the members of the list
        // that ARE NOT just lists of expressions. 
        //.cases
        
        Set<JmlMethodClauseExpr> intersection = new HashSet<JmlMethodClauseExpr>();
        
        for(List<JmlSpecificationCase> cases = tree.cases; cases.nonEmpty(); cases = cases.tail ){
            
            
            Set<JmlMethodClauseExpr> thisGroup = new HashSet<JmlMethodClauseExpr>();
            
                
            // it's nested (but must be previously computed)
            if(cases.head.clauses.head instanceof JmlMethodClauseGroup){
                Set<JmlMethodClauseExpr> join = joins.get(cases.head.clauses.head);
                
                if(join==null){
                    return null;
                }else{
                    thisGroup.addAll(join);
                }
            }
            // case 2, it's a set of all JmlSpecificationCases comprised of MethodClauseExpressions
            else{
                
                
                for(List<JmlMethodClause> clauses = cases.head.clauses; clauses.nonEmpty(); clauses = clauses.tail){
                    
                    if(clauses.head instanceof JmlMethodClauseExpr){
                        thisGroup.add((JmlMethodClauseExpr)clauses.head);
                    }                    
                }
                
            }
            if(intersection.size()==0){
                intersection.addAll(thisGroup);
            }else{
                computeIntersectionWith(intersection, thisGroup);
            }
            
        }
        
        return intersection;
    }

    public void computeIntersectionWith(Set<JmlMethodClauseExpr> intersection, Set<JmlMethodClauseExpr> thisGroup){
        
        Map<String,JmlMethodClauseExpr> us = new HashMap<String,JmlMethodClauseExpr>();
        Map<String,JmlMethodClauseExpr> them = new HashMap<String,JmlMethodClauseExpr>();
        
        for(JmlMethodClauseExpr e : intersection){
            us.put(e.toString(), e);
        }
        
        for(JmlMethodClauseExpr e : thisGroup){
            them.put(e.toString(), e);
        }
        
        for(String s : us.keySet()){
            if(them.keySet().contains(s)==false){
                intersection.remove(us.get(s));
            }
        }
        
    }

    // step 1 here is to find the reverse graph. this is used just to find that. 
    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        //log.getWriter(WriterKind.NOTICE).println(">Group Start<");
        //log.getWriter(WriterKind.NOTICE).println(tree.toString());
        path.add(tree);
        //log.getWriter(WriterKind.NOTICE).println(">Group End<");

        super.visitJmlMethodClauseGroup(tree);
    }
    
    public static void analyze(JCTree tree){
        
        FactorExpressionsAnalysis analysis = new FactorExpressionsAnalysis(Strongarm._context);
        analysis.doAnalysis(tree);
    }


    public static void analyze(JCTree tree, Context ctx, JmlTokenKind kind){
        
        FactorExpressionsAnalysis analysis = new FactorExpressionsAnalysis(ctx);
        analysis.doAnalysis(tree);
    }
}
