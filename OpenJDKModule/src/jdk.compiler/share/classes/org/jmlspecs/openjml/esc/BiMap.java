package org.jmlspecs.openjml.esc;

import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.openjml.Utils;

// FIXME - document
public class BiMap<T1,T2> {
    Map<T1,T2> forward = new HashMap<T1, T2>();
    Map<T2,T1> reverse = new HashMap<T2, T1>();
    
    public void put(T1 t1, T2 t2) {
        forward.put(t1, t2);
        reverse.put(t2, t1);
    }
    
    public void putf(T1 t1, T2 t2) {
        forward.put(t1, t2);
    }
    
    public T2 getf(T1 t) {
        return forward.get(t);
    }
    
    public T1 getr(T2 t) {
        return reverse.get(t);
    }
    
    public void clear() {
        forward.clear();
        reverse.clear();
    }
    
    public <T3> BiMap<T1,T3> compose(BiMap<T2,T3> bimap) {
        BiMap<T1,T3> newmap = new BiMap<T1,T3>();
        for (T1 t1: forward.keySet()) {
            T2 t2 = getf(t1);
            T3 t3 = bimap.getf(t2);
            if (t3 != null) newmap.put(t1, t3);
        }
        return newmap;
    }
    
    public <T3> Map<T1,T3> compose(Map<T2,T3> bimap) {
        Map<T1,T3> newmap = new HashMap<T1,T3>();
        for (T1 t1: forward.keySet()) {
            T2 t2 = getf(t1);
            T3 t3 = bimap.get(t2);
            newmap.put(t1, t3);
        }
        return newmap;
    }
}