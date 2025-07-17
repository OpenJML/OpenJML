package org.jmlspecs.lang.internal;
import java.util.*;
import org.jmlspecs.lang.IJmlPrimitiveType;
import org.jmlspecs.lang.IJmlArrayLike;

//@ immutable no_state 
public class set<T> implements IJmlPrimitiveType, IJmlArrayLike {
    
    private final Set<T> value;
    
    private set() { value = new HashSet<>(); }

    private set(Set<T> data) { value = data; }
    
    private set<T> copy() {
        return new set<T>(new HashSet<T>(value));
    }

    static public <T> set<T> empty() { return new set<T>(); }

    public bigint size() { return bigint.of(value.size()); }

    @SafeVarargs
    @SuppressWarnings("unchecked")
    static public <X> set<X> of(X ... data) {
        var s = new set<X>();
        for (var i: data) s.value.add(i);
        return s;
    }
    
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
        return size().eq(bigint.zero);
    }
    
    @Override
    public boolean equals(Object s) {
        throw new UnsupportedOperationException("\\set.equals");
    }
    
    @Override
    public int hashCode() {
        return value.hashCode();
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
    
    
    public set<T> union(set<T> s) {
        var r = this.copy();
        r.value.addAll(s.value);
        return r;
    }

    public set<T> intersect(set<T> s) {
        var r = this.copy();
        r.value.retainAll(s.value);
        return r;
    }

    public set<T> subtract(set<T> s) {
        var r = this.copy();
        r.value.removeAll(s.value);
        return r;
    }

}