package org.jmlspecs.lang;

import java.util.*;
import org.jmlspecs.lang.internal.*;

//@ immutable pure 
public class intset implements IJmlPrimitiveType, IJmlIntArrayLike {
    
    private Set<bigint> value = new HashSet<>();
    
    private intset() { value = new HashSet<bigint>(); }

    private intset(Set<bigint> data) { value = data; }

    private intset copy() { return new intset(new HashSet<bigint>(value)); }
        
    public static intset empty() { return new intset(); }
    
    public boolean eq(intset a) {
        return value.equals(a.value);
    }
    
    public boolean ne(intset a) {
        return !eq(a);
    }
    
    public boolean has(bigint k) {
        return value.contains(k);
    }
    
    public intset add(bigint k) {
        var copy = new HashSet<bigint>(value);
        copy.add(k);
        return new intset(copy);
    }
    
    public intset put(bigint k, boolean b) {
        var copy = copy();
        if (b) copy.value.add(k); else copy.value.remove(k);
        return copy;
    }
    
    public intset remove(bigint k) {
        var copy = copy();
        copy.value.remove(k);
        return copy;
    }
    
    public intset union(intset a) {
        var copy = copy();
        copy.value.addAll(a.value);
        return copy;
    }
    
    public intset intersection(intset a) {
        var copy = copy();
        copy.value.retainAll(a.value);
        return copy;
    }
    
    public intset difference(intset a) {
        var copy = copy();
        copy.value.removeAll(a.value);
        return copy;
    }
}
