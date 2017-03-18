package org.jmlspecs.openjml.strongarm;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;

import org.jmlspecs.openjml.JmlTree.JmlMethodClause;

import com.sun.tools.javac.util.List;

public class JDKListUtils {
    
    static public <T> List<T> sort(List<T> from, Comparator<T> c){
        
        ArrayList<T> l = new ArrayList<T>();
        List<T> newList = null;
        
        for(List<T> e = from; e.nonEmpty(); e = e.tail){
            l.add(e.head);
        }
            
        Collections.sort(l,c);
        
        for(T e : l){
            if(newList==null){
                newList = List.of(e);
            }else{
                newList = newList.append(e);
            }
        }
        
        return newList;
    }
    
    

    static public <T> List<T> toList(Collection<T> l){
        
        List<T> newList = null;
        
        for(T e : l){
            if(newList==null){
                newList = List.of(e);
            }else{
                newList = newList.append(e);
            }
        }
        
        return newList;
    }
    
    
    public static <T> boolean contains(List<T> theClauses, T clause, Comparator<T> c){
        
        
        for(List<T> clauses = theClauses; clauses.nonEmpty(); clauses = clauses.tail){
        
            if(c.compare(clauses.head, clause)==0){
                return true;
            }
        }
      
        return false;
    }

}
