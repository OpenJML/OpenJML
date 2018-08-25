package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.util.HashMap;
import java.util.Map;

public class AdjacencyMatrix<T> {

    private Map<T, HashMap<T, Integer>> matrix = new HashMap<T,HashMap<T,Integer>>();
    
    public void add(T a, T b, int weight){
        
        if(matrix.get(a)==null){
            matrix.put(a, new HashMap<T,Integer>());
        }
        
        matrix.get(a).put(b, weight);
    }
    
    public boolean isConnected(T a, T b){
        return weight(a,b) > 0;
    }
    
    public int weight(T a, T b){
        
        if(matrix.get(a)!=null && matrix.get(a).get(b)!=null){
            return matrix.get(a).get(b);
        }
        
        return 0;
    }
}
