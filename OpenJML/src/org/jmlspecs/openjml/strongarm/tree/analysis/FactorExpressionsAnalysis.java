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
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.strongarm.Strongarm;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log.WriterKind;

public class FactorExpressionsAnalysis extends JmlTreeAnalysis {

    public FactorExpressionsAnalysis(Context context) {
        super(context);
    }

    private ArrayList<JmlMethodClauseGroup>                     path  = new ArrayList<JmlMethodClauseGroup>();

    private Map<JmlMethodClauseGroup, Set<JmlMethodClause>> joins = new HashMap<JmlMethodClauseGroup, Set<JmlMethodClause>>();

    private ArrayList<JmlMethodClauseGroup> reverseGraph() {

        ArrayList<JmlMethodClauseGroup> r = new ArrayList<JmlMethodClauseGroup>(
                path);

        Collections.reverse(r);

        return r;
    }

    private void printIntersectionMap() {

        if (verbose) {

            for (JmlMethodClauseGroup k : joins.keySet()) {

                log.getWriter(WriterKind.NOTICE).println(">Group Start<");

                log.getWriter(WriterKind.NOTICE).println(k.toString());

                log.getWriter(WriterKind.NOTICE).println("Intersections:");

                for (JmlMethodClause e : joins.get(k)) {
                    log.getWriter(WriterKind.NOTICE)
                            .println("\t -> " + e.toString());
                }

                log.getWriter(WriterKind.NOTICE).println(">Group End<");

            }

        }
    }

    private void doAnalysis(JCTree tree) {
        // step 1
        // find the reverse graph
        scan(tree);

        ArrayList<JmlMethodClauseGroup> R = reverseGraph();

        // step 2
        // next, for each join (OR), find the intersection of the sets of
        // propositions.
        // for each join point, we require that (if it's not a block of
        // statements) that
        // the join point has been previously computed.

        Map<JmlMethodClauseGroup, Set<JmlMethodClauseExpr>> blockMap = new HashMap<JmlMethodClauseGroup, Set<JmlMethodClauseExpr>>();

        while (R.size() > 0) { // fixpoint
            for (Iterator<JmlMethodClauseGroup> iterator = R
                    .iterator(); iterator.hasNext();) {

                JmlMethodClauseGroup G = iterator.next();

                Set<JmlMethodClause> intersection = getIntersection(G);

                if (intersection != null) {
                    joins.put(G, intersection);
                    iterator.remove();
                }

            }
        }

        printIntersectionMap();
        
        log.getWriter(WriterKind.NOTICE).println(">==========================<");


        // step 3 "bubbling"
        // at this point, we should have computed all of the intersections.
        // we could stop here and have a slightly reduced contract; however, to
        // maximize
        // the reduction in the size of the contract, we "bubble" up things in
        // the intersection
        // that exist in the intersection of a child clause, but not necessarily
        // in the parent.
        // of course, it is possible that contradictory statements could be in
        // the group we are trying
        // to bubble to that contradict the clause we are bubbling. to prevent
        // this, we make sure there
        // are no conflicts prior to adding it to the intersections.

        // the effect of this stage is to increase the size of the intersection
        // set
        // we repeat the bubbling until the size fo the intersections doesn't
        // change.
        int previousSize = 0;
        do {
            previousSize = joins.values().stream().mapToInt(x -> x.size()).sum();

            R = reverseGraph();

            for (Iterator<JmlMethodClauseGroup> iterator = R
                    .iterator(); iterator.hasNext();) {

                JmlMethodClauseGroup G = iterator.next();

                bubble(G);

            }

        } while (joins.values().stream().mapToInt(x -> x.size()).sum() != previousSize);

        printIntersectionMap();
        
        // step 4 "merging"
        //
        // the merge consists of two parts
        //
        // 1) for TOPLEVEL groups, we inspect the intersections. for each entry, 
        //    if the expression isn't already there, we add it. This is the merged set. 
        // 2) For each merged expression, in the child specifications we remove 
        //    any of the merged expressions from the contract. 
        for (Iterator<JmlMethodClauseGroup> iterator = R
                .iterator(); iterator.hasNext();) {

            JmlMethodClauseGroup G = iterator.next();
            
            merge(G);
        }

    }

    // the merge consists of two parts
    //
    // 1) for TOPLEVEL groups, we inspect the intersections. for each entry, 
    //    if the expression isn't already there, we add it. This is the merged set. 
    // 2) For each merged expression, in the child specifications we remove 
    //    any of the merged expressions from the contract.   
    private void merge(JmlMethodClauseGroup tree) {
          
        // we only care about joins where the top level element can be merged.
        if(!(tree.cases.head.clauses.head instanceof JmlMethodClauseExpr))
        {
            return;
        }
        
        // this represents the set of expressions we need to merge
        Set<JmlMethodClause> intersection = joins.get(tree);

  
        ArrayList<JmlMethodClause> toAdd = new ArrayList<JmlMethodClause>();
        ArrayList<JmlMethodClause> exprs = new ArrayList<JmlMethodClause>();
        
        
        
        // first, add these expressions if they DO NOT already exist in the top 
        // level set of expressions.
        for (List<JmlMethodClause> es = tree.cases.head.clauses; es
                .nonEmpty(); es = es.tail) {

            //String exprString = es.head.toString();
            
            exprs.add(es.head);
            
        }    
        
        for(JmlMethodClause a : intersection){
            
            boolean exists = exprs.stream()
                    .filter(x -> x.toString().equals(a.toString()))
                    .findFirst()
                    .isPresent();
            

            // if it doesn't exist, append
            if(!exists){
                tree.cases.head.clauses = tree.cases.head.clauses.append(a);
            }
            
        }
        
        // next REMOVE any of the expressions in the child clauses 
        if(tree.cases.tail!=null){
            FilterExpressions.analyze(tree.cases.tail.head, intersection);
        }
        
        
        if(1==1){
            System.out.println("");
        }
        
        
//        for (List<JmlSpecificationCase> cases = tree.cases; cases
//                .nonEmpty(); cases = cases.tail) {
//
//            Set<JmlMethodClauseExpr> thisGroup = new HashSet<JmlMethodClauseExpr>();
//
//            
//            if (cases.head.clauses.head instanceof JmlMethodClauseExpr) {
//                
//            }else{
//                return;
//            }
//
//        }        
    }

    private void bubble(JmlMethodClauseGroup tree) {

        Set<JmlMethodClause> intersection = joins.get(tree);
        JmlSpecificationCase last = null;
        
        for (List<JmlSpecificationCase> cases = tree.cases; cases
                .nonEmpty(); cases = cases.tail) {

            Set<JmlMethodClauseExpr> thisGroup = new HashSet<JmlMethodClauseExpr>();

            
            // it's nested (but must be previously computed)
            // this is the case we are looking at expanding.
            if (cases.head.clauses.head instanceof JmlMethodClauseGroup) {
                
                Set<JmlMethodClause> join = joins
                        .get(cases.head.clauses.head);

                // if for some reason there isn't a previous 
                // set, let's create it now.
                if(join == null){
                    join = new HashSet<JmlMethodClause>();
                    joins.put((JmlMethodClauseGroup)cases.head.clauses.head, join);

                }

                
                // what we are looking for here 
                // are things that are in the intersection of some child group
                // if the PARENT doesn't explicity say something 
                // about the variables in the given expression 
                // we add it to the intersections.
                
                computeAdditiveIntersection(last, intersection, join);
            }else{
                last = cases.head;
            }

        }
        
        joins.put(tree,  intersection);

    }

    private void computeAdditiveIntersection(
            JmlSpecificationCase last, Set<JmlMethodClause> intersection,
            Set<JmlMethodClause> B) {
       
        
        Map<String, JmlMethodClause> us = new HashMap<String, JmlMethodClause>();
        Map<String, JmlMethodClause> them = new HashMap<String, JmlMethodClause>();

        for (JmlMethodClause e : intersection) {
            us.put(e.toString(), e);
        }

        for (JmlMethodClause e : B) {
            them.put(e.toString(), e);
            
            // convert subexpressions
            Set<JCIdent> idents = new HashSet<JCIdent>();
            
            if(e instanceof JmlMethodClauseExpr){
                idents = GetIdentsAnalysis.analyze(((JmlMethodClauseExpr)e).expression);
            }else if(e instanceof JmlMethodClauseStoreRef) {
                
                JmlMethodClauseStoreRef ref = (JmlMethodClauseStoreRef)e;
                
                idents = GetIdentsAnalysis.analyze(ref.list);
            }
            
            for(JCIdent id : idents){
                them.put(id.toString(), e);
            }
            
            
        }
        
        Set<JCIdent> parentIdents = GetIdentsAnalysis.analyze(last);
        Set<String> parents = new HashSet<String>();

        for(JCIdent p : parentIdents){
            parents.add(p.toString());
        }
        
        // look for things that are in B, but not in any subexpression in intersection. 
        for(String t : them.keySet()){
            
            if(keyContains(t, us.keySet())==false && intersection.contains(them.get(t))==false){
                
                // for the moment, we do something not so brilliant
                // in that we consider ANY reference of an ident 
                // to violate data integrity. 
               
                if(parents.contains(t)==false && (keyContains(t, parents)==false || them.get(t) instanceof JmlMethodClauseStoreRef) ){
                    intersection.add(them.get(t));
                }
                
                
            }
            
                
        }
        
    }
    
    
    
    private boolean keyContains(String needle, Set<String> haystack)
    {
        for(String s : haystack){
            if(s.contains(needle) || needle.contains(s)){
                return true;
            }
        }
        return false;
    }

    private Set<JmlMethodClause> getIntersection(
            JmlMethodClauseGroup tree) {

        // the precondition for getting the intersection is that either
        // a) ALL parts of the group are lists of expressions
        // or
        // b) We have computed an intersection for the members of the list
        // that ARE NOT just lists of expressions.
        // .cases

        Set<JmlMethodClause> intersection = new HashSet<JmlMethodClause>();

        for (List<JmlSpecificationCase> cases = tree.cases; cases
                .nonEmpty(); cases = cases.tail) {

            Set<JmlMethodClause> thisGroup = new HashSet<JmlMethodClause>();

            // it's nested (but must be previously computed)
            if (cases.head.clauses.head instanceof JmlMethodClauseGroup) {
                Set<JmlMethodClause> join = joins
                        .get(cases.head.clauses.head);

                if (join == null) {
                    return null;
                } else {
                    thisGroup.addAll(join);
                }
            }
            // case 2, it's a set of all JmlSpecificationCases comprised of
            // MethodClauseExpressions
            else {

                for (List<JmlMethodClause> clauses = cases.head.clauses; clauses
                        .nonEmpty(); clauses = clauses.tail) {

                    if (clauses.head instanceof JmlMethodClauseExpr || clauses.head instanceof JmlMethodClauseStoreRef) {
                        thisGroup.add(clauses.head);
                    }
                }

            }
            if (intersection.size() == 0) {
                intersection.addAll(thisGroup);
            } else {
                computeIntersectionWith(intersection, thisGroup);
            }

        }

        return intersection;
    }

    public void computeIntersectionWith(Set<JmlMethodClause> intersection,
            Set<JmlMethodClause> thisGroup) {

        Map<String, JmlMethodClause> us = new HashMap<String, JmlMethodClause>();
        Map<String, JmlMethodClause> them = new HashMap<String, JmlMethodClause>();

        for (JmlMethodClause e : intersection) {
            us.put(e.toString(), e);
        }

        for (JmlMethodClause e : thisGroup) {
            them.put(e.toString(), e);
        }

        for (String s : us.keySet()) {
            if (them.keySet().contains(s) == false) {
                intersection.remove(us.get(s));
            }
        }

    }

    // step 1 here is to find the reverse graph. this is used just to find that.
    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        // log.getWriter(WriterKind.NOTICE).println(">Group Start<");
        // log.getWriter(WriterKind.NOTICE).println(tree.toString());
        path.add(tree);
        // log.getWriter(WriterKind.NOTICE).println(">Group End<");

        super.visitJmlMethodClauseGroup(tree);
    }

    public static void analyze(JCTree tree) {

        FactorExpressionsAnalysis analysis = new FactorExpressionsAnalysis(
                Strongarm._context);
        analysis.doAnalysis(tree);
    }

    public static void analyze(JCTree tree, Context ctx, JmlTokenKind kind) {

        FactorExpressionsAnalysis analysis = new FactorExpressionsAnalysis(ctx);
        analysis.doAnalysis(tree);
    }
}
