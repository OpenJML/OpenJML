package org.jmlspecs.lang.internal;

import org.jmlspecs.lang.IJmlPrimitiveType;
import org.jmlspecs.lang.IJmlArrayLike;
import java.util.*;

//@ immutable no_state non_null_by_default
public class map<K,V> implements IJmlPrimitiveType, IJmlArrayLike {
    
    private final HashMap<K,V> value;
    
    private map() { value = new HashMap<K,V>(); }
    
    private map(HashMap<K,V> data) { value = data; }

    /** Constructs an empty map */
    public static <KK,VV> map<KK,VV> empty() { return new map<KK,VV>(); }
    
    /**  Returns true iff the map is empty */
    public boolean isEmpty() { return value.size() == 0; }
    
    /** Returns the number of entries in the map */
    public bigint size() { return bigint.of(value.size()); }

    /** Returns true iff the value k is a key in the map */
    public boolean has(K k) { return value.containsKey(k); }
    
    /** Returns the value associated with the key k; result is undefined if k is not a key in the map. */
    //@ nullable
    public V get(K k) { return value.get(k); }
    
    /** Returns a new map that is a copy of the receiver, with an additional (or replacement) mapping */
    public map<K,V> put(K k, V v) { 
        var c = new HashMap<K,V>(value);
        c.put(k,v);
        return new map<K,V>(c);
    }
    
    /** Returns a new map that is a copy of the receiver with the mapping for key k removed */
    public map<K,V> remove(K k) { 
        if (!this.value.containsKey(k)) return this;
        var c = new HashMap<K,V>(value);
        c.remove(k);
        return new map<K,V>(c);
    }
    
    /** Returns a new map that is a copy of the receiver with all of the mappings in the argument added in */
    public map<K,V> putAll(map<K,V> m) {
        var c = new HashMap<K,V>(value);
        c.putAll(m.value);
        return new map<K,V>(c);
    }
    
    /** Returns the domain of the map (the set of all keys)*/
    public set<K> keys() {
        return set.<K>of(this.value.keySet());
    }
    
    /** Returns true iff the receiver and argument have all the same mappings */
    public boolean eq(map<K,V> m) { return value.equals(m.value); }
    
    /** Negation of eq(m) */
    public boolean ne(map<K,V> m) { return !eq(m); }

    /** Same as eq(m) */
    public boolean equals(map<K,V> m) {
        return eq(m);
    }
    
    /** Only meant to support using this class in hashed sets and maps; use eq to compare maps */ 
    @SuppressWarnings("unchecked")
    @Override
    public boolean equals(Object o) {
        return (o instanceof map<?,?> mm) && eq((map<K,V>)mm);
    }
    
    /** Only meant to support using instances of this class in hashed sets and maps */
    @Override
    public int hashCode() {
        return value.hashCode();
    }
    
    /** Returns a String representation of the instance */
    @Override
    public String toString() {
        return value.toString();
    }
}
