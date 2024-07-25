package org.jmlspecs.lang;
import java.util.*;

//@ immutable pure 
public class set<T> implements IJmlPrimitiveType, IJmlArrayLike {
    
    private final Set<T> value;
    
    private set(Set<T> data) { value = data; }
    
    private set<T> copy() {
        return new set<T>(new HashSet<T>(value));
    }

    public set() { value = new HashSet<>(); }
    
    static public <T> set<T> empty() { return new set<T>(); }

    public long size() { return value.size(); }

    //@ public normal_behavior
    //@   ensures \result == (\forall T t;; this.contains(t) == ss.contains(t));
    //@ no_state
    public boolean eq(set<T> ss) {
        return value.equals(ss.value); // FIXME - what kind of equals to use
    }
    
    //@ public normal_behavior
    //@   ensures \result != (\forall T t;; this.contains(t) == ss.contains(t));
    //@ no_state
    public boolean ne(set<T> ss) {
        return !value.equals(ss.value); // FIXME - what kind of equals to use
    }
    
 
    //@ public normal_behavior
    //@   ensures \result == this[x];
    //@ no_state
    public boolean contains(T x) {
        return value.contains(x);
    }

    //@ public normal_behavior
    //@   ensures \result == (this.size() == 0);
    //@ no_state
    public boolean isEmpty() {
        return size() == 0;
    }
    
    //@ public normal_behavior
    //@   ensures \result.size() == 1;
    //@  ensures \result.contains(t);
    //@  ensures (\forall X x; ; x != t ==> !\result.contains(x));
    //@ no_state
    @SafeVarargs
    static public <X> set<X> of(X ... t) {
        var s = new set<X>();
        for (var i: t) s.value.add(i);
        return s;
    }

    
    //@ public normal_behavior
    //@   ensures \result == (this == s || equals(this,s));
    //@ no_state
    public boolean equals(set<T> s) {
        return this.value.equals(s.value);
    }

    //@ public normal_behavior
    //@   ensures \result == (\forall T t; this.contains(t) ; s.contains(t));
    //@ no_state
    public boolean isSubsetOf(set<T> s) {
        for (var k: s.value) if (!s.value.contains(k)) return false;
        return true;
    }
    
    //@ public normal_behavior
    //@   ensures this.contains(x) ==> \result == this;
    //@   ensures !this.contains(x) ==> \result.size() == this.size() + 1;
    //@   ensures \result.contains(x);
    //@   ensures (\forall T t; t != x; \result.contains(t) == this.contains(t));
    //@ no_state
    public set<T> add(T x) {
        var c = this.copy();
        c.value.add(x);
        return c;
    }
    
    //@ public normal_behavior
    //@   ensures !this.contains(x) ==> \result == this;
    //@   ensures this.contains(x) ==> \result.size() == this.size() - 1;
    //@   ensures !\result.contains(x);
    //@   ensures (\forall T t; t != x; \result.contains(t) == this.contains(t));
    //@ no_state
    public set<T> remove(T x) {
        var c = this.copy();
        c.value.remove(x);
        return c;
    }

    //@ public normal_behavior
    //@   ensures \forall T j; this.contains(j);  p.apply(j) ==> \result.contains(j));
    //@   ensures \forall T j; \result.contains(j) ==> (this.contains(j) && p.test(j);
    //@ no_state
    public set<T> filter(java.util.function.Predicate<T> p) {
        var c = new set<T>();
        for (var x: this.value) if (p.test(x)) c.value.add(x);
        return c;
    }

}