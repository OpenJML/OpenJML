package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
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
import org.jmlspecs.openjml.ext.MethodExprClauseExtensions;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.sun.tools.javac.util.List;

public class SpecBlockVertex  {
    
    public ArrayList<JmlMethodClause>  clauses = new ArrayList<JmlMethodClause>();
    public Map<String,JmlMethodClause> cache     = new HashMap<String,JmlMethodClause>();
    public JmlSpecificationCase basedOn;
    private boolean conjunction;
    private boolean allowAnyOrder;
    
    public SpecBlockVertex(JmlSpecificationCase basedOn){
        this(basedOn, true);
        
    }

    public SpecBlockVertex(JmlSpecificationCase basedOn, boolean allowAnyOrder){
        this.basedOn = basedOn;        
        this.allowAnyOrder = allowAnyOrder;
        this.buildCache();
    }

    
    public SpecBlockVertex(boolean isConjunction){
        this(isConjunction, true);
    }
    
    public SpecBlockVertex(boolean isConjunction, boolean allowAnyOrder){
        this.conjunction = isConjunction;
        this.allowAnyOrder = allowAnyOrder;
    }
    
    public boolean isConjunction(){
        return conjunction;
    }
    
    public boolean isAllowAnyOrder(){
        return allowAnyOrder;
    }
    
    private void buildCache(){
    
        cache.clear();
        clauses.clear();
        
        
        // rebuild the cache
        for(List<JmlMethodClause> clause = basedOn.clauses; clause.nonEmpty(); clause = clause.tail){
            if(clause.head!=null && ((clause.head instanceof JmlMethodClauseExpr) || (clause.head instanceof JmlMethodClauseStoreRef))){
                String stringRep = clause.head.toString();
                
                if(!stringRep.contains("requires !(false)") && !stringRep.contains("requires !false")){                
                    add(clause.head);
                }
            }
        }
    }
    
    public void add(JmlMethodClause m){
        cache.put(m.toString().trim(), m);
        clauses.add(m);
    }
    
    public void removeAll(Collection<JmlMethodClause> cs){
        for(JmlMethodClause c : cs){
            remove(c);
        }
    }
    
    public void addAll(Collection<JmlMethodClause> cs){
        for(JmlMethodClause c : cs){
            add(c);
        }
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
        return cache.containsKey(m.trim());
    }
    
    public boolean contains(JmlMethodClause m){
        return contains(m.toString().trim());
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
            
            // there are two ways to do it
            
            if(isAllowAnyOrder()==false){
                if(c.clauseKind == requiresClauseKind && v.contains(c)){
                    theIntersection.add(c);
                }
            }else{    
                if(v.contains(c)){
                    theIntersection.add(c);
                }
            }
        }
        
        
        return theIntersection;
    }

    public static String toJSON(Collection<SpecBlockVertex> vs)  {
        
        ArrayList<SpecBlockDTO> dtos = new ArrayList<SpecBlockDTO>();
        
        for(SpecBlockVertex v : vs) {
            
            SpecBlockDTO dto = new SpecBlockDTO();
            
            dto.type = "dis";
            
            for(JmlMethodClause c : v.clauses){
                if(c instanceof JmlMethodClauseExpr ||  c instanceof JmlMethodClauseStoreRef){
                    dto.clauses.add(c.toString());
                }        
            }

            
            dtos.add(dto);
        }
        
        
        Gson gson = new GsonBuilder().disableHtmlEscaping().create();
        
        String buff =  gson.toJson(dtos);
        
        
        return buff;
    }
    
    @Override
    public String toString() {
       
        StringBuffer sb = new StringBuffer();        
        
        if(isConjunction() && clauses.size() > 0){
            sb.append("^\n");
        }else{
            sb.append("v\n");
        }
        
        for(JmlMethodClause c : clauses){
            if(c instanceof JmlMethodClauseExpr ||  c instanceof JmlMethodClauseStoreRef){
                sb.append(c.toString() + "\n");
            }        
        }
        
//        for(List<JmlMethodClause> clauses = basedOn.clauses; clauses.nonEmpty(); clauses = clauses.tail){
//            
//            if(clauses.head instanceof JmlMethodClauseExpr ||  clauses.head instanceof JmlMethodClauseStoreRef){
//                sb.append(clauses.head.toString() + "\n");
//            }
//            
//        }
        return sb.toString();
    }
    
}

