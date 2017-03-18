package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;

import com.sun.tools.javac.util.List;

public class SpecBlockVertex  {
    
    public ArrayList<JmlMethodClause>  clauses = new ArrayList<JmlMethodClause>();
    public Map<String,JmlMethodClause> cache     = new HashMap<String,JmlMethodClause>();
    public JmlSpecificationCase basedOn;
    public SpecBlockVertex(JmlSpecificationCase basedOn){
        this.basedOn = basedOn;        
        this.buildCache();
    }
    
        
    private void buildCache(){
    
        cache.clear();
        clauses.clear();
        
        
        // rebuild the cache
        for(List<JmlMethodClause> clause = basedOn.clauses; clause.nonEmpty(); clause = clause.tail){
            if(clause.head!=null && ((clause.head instanceof JmlMethodClauseExpr) || (clause.head instanceof JmlMethodClauseStoreRef))){
                add(clause.head);
            }
        }
    }
    
    public void add(JmlMethodClause m){
        cache.put(m.toString(), m);
        clauses.add(m);
    }
    
    public void remove(JmlMethodClause m){
        
        cache.remove(m.toString());
        
        Iterator<JmlMethodClause> it = clauses.iterator();
        
        while(it.hasNext()){
            if(it.next().toString().equals(m.toString())){
                it.remove();
            }
        }
        
    }
    
    public boolean contains(String m){
        return cache.containsKey(m);
    }
    
    public boolean contains(JmlMethodClause m){
        return contains(m.toString());
    }
    
    public boolean containsClauseByRef(JmlMethodClause m){
        return clauses.contains(m);
    }
    
    public ArrayList<JmlMethodClause> getClauses(){
        return clauses;
    }
    
    public Set<JmlMethodClause> intersection(SpecBlockVertex v){
        Set<JmlMethodClause> theIntersection = new HashSet<JmlMethodClause>();
        
        
        for(JmlMethodClause c : getClauses()){
            if(c.token == JmlTokenKind.REQUIRES && v.contains(c)){
                theIntersection.add(c);
            }
        }
        
        
        return theIntersection;
    }

    @Override
    public String toString() {
       
        StringBuffer sb = new StringBuffer();        
        
        for(List<JmlMethodClause> clauses = basedOn.clauses; clauses.nonEmpty(); clauses = clauses.tail){
            
            if(clauses.head instanceof JmlMethodClauseExpr ||  clauses.head instanceof JmlMethodClauseStoreRef){
                sb.append(clauses.head.toString() + "\n");
            }
            
        }
        return sb.toString();
    }
    
    
}

