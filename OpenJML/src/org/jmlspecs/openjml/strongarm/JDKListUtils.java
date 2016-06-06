package org.jmlspecs.openjml.strongarm;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
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

}
