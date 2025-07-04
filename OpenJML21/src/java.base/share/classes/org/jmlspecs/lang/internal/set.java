package org.jmlspecs.lang.internal;
import java.util.*;
import org.jmlspecs.lang.IJmlPrimitiveType;
import org.jmlspecs.lang.IJmlArrayLike;

//@ immutable no_state 
public class set<T> implements IJmlPrimitiveType, IJmlArrayLike {
    
    private final Set<T> value;
    
    private set(Set<T> data) { value = data; }
    
    private set<T> copy() {
        return new set<T>(new HashSet<T>(value));
    }

    public set() { value = new HashSet<>(); }
    
    static public <T> set<T> empty() { return new set<T>(); }

    public long size() { return value.size(); }

    public boolean eq(set<T> ss) {
        return value.equals(ss.value); // FIXME - what kind of equals to use
    }
    
    public boolean ne(set<T> ss) {
        return !value.equals(ss.value); // FIXME - what kind of equals to use
    }
    
 
    public boolean contains(T x) {
        return value.contains(x);
    }

    public boolean isEmpty() {
        return size() == 0;
    }
    
    @SafeVarargs
    static public <X> set<X> of(X ... t) {
        var s = new set<X>();
        for (var i: t) s.value.add(i);
        return s;
    }

    public boolean equals(set<T> s) {
        throw new UnsupportedOperationException("\\set.equals");
    }

    public boolean isSubsetOf(set<T> s) {
        for (var k: s.value) if (!s.value.contains(k)) return false;
        return true;
    }
    
    public set<T> add(T x) {
        var c = this.copy();
        c.value.add(x);
        return c;
    }
    
    public set<T> remove(T x) {
        var c = this.copy();
        c.value.remove(x);
        return c;
    }

    public set<T> filter(java.util.function.Predicate<T> p) {
        var c = new set<T>();
        for (var x: this.value) if (p.test(x)) c.value.add(x);
        return c;
    }
    
    private set<T> put(T x, boolean b) { return this; } // FIXME


}