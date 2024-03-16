package org.jmlspecs.lang;
import java.util.*;

//@ immutable pure 
public class set<T> implements IJmlPrimitiveType, IJmlArrayLike {
    
    private final HashSet<T> value;

    public set() { value = new HashSet<>(); }
    
    static public <T> set<T> set() { return new set<T>(); }

    public long size() { return value.size(); }
 /*   
    //@ public normal_behavior
    //@   ensures \result == this[x];
    //@ no_state
    public boolean contains(T x);

    //@ public normal_behavior
    //@   ensures \result == (this.size() == 0);
    //@ no_state
    public boolean isEmpty();
    
    
    //@ public normal_behavior
    //@   ensures \result.size() == 1;
    //@  ensures \result.contains(t);
    //@  ensures (\forall T x; ; x != t ==> !\result.contains(x));
    //@ no_state
    static public <T> set<T> set(T t);
    
    //@ public normal_behavior
    //@   ensures \result == (\forall T t;; s.contains(t) == ss.contains(t));
    //@ no_state
    public static <T> boolean eq(set<T> s, set<T> ss);
    
    //@ public normal_behavior
    //@   ensures \result == (this == s || equals(this,s));
    //@ no_state
    public boolean equals(set<T> s);
    
    //@ public normal_behavior
    //@   ensures \result == (\forall T t; s.contains(t) ; ss.contains(t));
    //@ no_state
    public static <T> boolean isSubsetOf(set<T> s, set<T> ss);
    
    //@ public normal_behavior
    //@   ensures this.contains(x) ==> \result == this;
    //@   ensures !this.contains(x) ==> \result.size() == this.size() + 1;
    //@   ensures \result.contains(x);
    //@   ensures (\forall T t; t != x; \result.contains(t) == this.contains(t));
    //@ no_state
    public set<T> add(T x);
    
    //@ public normal_behavior
    //@   ensures !this.contains(x) ==> \result == this;
    //@   ensures this.contains(x) ==> \result.size() == this.size() - 1;
    //@   ensures !\result.contains(x);
    //@   ensures (\forall T t; t != x; \result.contains(t) == this.contains(t));
    //@ no_state
    public set<T> remove(T x);

    //@ public normal_behavior
    //@   ensures \forall T j; this.contains(j);  p.apply(j) ==> \result.contains(j));
    //@   ensures \forall T j; \result.contains(j) ==> (this.contains(j) && p.apply(j);
    //@ no_state
    public set<T> filter(java.util.function.Predicate<T> p);}
*/
}