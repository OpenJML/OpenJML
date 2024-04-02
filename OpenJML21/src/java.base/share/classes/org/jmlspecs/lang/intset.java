package org.jmlspecs.lang;

import java.util.*;

//@ immutable pure 
public class intset implements IJmlPrimitiveType, IJmlIntArrayLike {
    
    private Set<Integer> value = new HashSet<>();  // FIXME - change to bigint
    
    private intset() { value = new HashSet<Integer>(); }

    private intset(Set<Integer> data) { value = data; }
        
    public static intset empty() { return new intset(); }
    
    public boolean eq(intset a) {
        return value.equals(a.value);
    }
    
    public boolean ne(intset a) {
        return !eq(a);
    }
    
    public boolean has(int k) {
        return value.contains(k);
    }
    
    public intset add(int k) {
        var copy = new HashSet<Integer>(value);
        copy.add(k);
        return new intset(copy);
    }
    
    public intset put(int k, boolean b) {
        var copy = new HashSet<Integer>(value);
        if (b) copy.add(k); else copy.remove(k);
        return new intset(copy);
    }
    
    public intset remove(int k) {
        var copy = new HashSet<Integer>(value);
        copy.remove(k);
        return new intset(copy);
    }
    
    public intset union(intset a) {
        var copy = new HashSet<Integer>(value);
        copy.addAll(a.value);
        return new intset(copy);
    }
    
    public intset intersection(intset a) {
        var copy = new HashSet<Integer>(value);
        copy.retainAll(a.value);
        return new intset(copy);
    }
    
    public intset difference(intset a) {
        var copy = new HashSet<Integer>(value);
        copy.removeAll(a.value);
        return new intset(copy);
    }
}
