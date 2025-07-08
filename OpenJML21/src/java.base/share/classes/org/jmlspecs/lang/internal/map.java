package org.jmlspecs.lang.internal;

import org.jmlspecs.lang.IJmlPrimitiveType;
import org.jmlspecs.lang.IJmlArrayLike;
import java.util.*;

//@ immutable no_state non_null_by_default
public class map<K,V> implements IJmlPrimitiveType, IJmlArrayLike {
    
    private final HashMap<K,V> value;
    
    private map() { value = new HashMap<K,V>(); }
    
    private map(HashMap<K,V> data) { value = data; }

    public static <KK,VV> map<KK,VV> empty() { return new map<KK,VV>(); }
    
    public boolean isEmpty() { return value.size() == 0; }
    
    public bigint size() { return bigint.of(value.size()); }

    public boolean has(K k) { return value.containsKey(k); }
    
    //@ nullable
    public V get(K k) { return value.get(k); }
    
    public map<K,V> put(K k, V v) { 
        var c = new HashMap<K,V>(value);
        c.put(k,v);
        return new map<K,V>(c);
    }
    
    public map<K,V> remove(K k) { 
        if (!this.has(k)) return this;
        var c = new HashMap<K,V>(value);
        c.remove(k);
        return new map<K,V>(c);
    }
    
    
    public map<K,V> combine(map<K,V> m) {
        var c = new HashMap<K,V>(value);
        c.putAll(m.value);
        return new map<K,V>(c);
    }
    
    public boolean eq(map<K,V> m) { return value.equals(m.value); }
    
    public boolean ne(map<K,V> m) { return !eq(m); }

    
    @SuppressWarnings("unchecked")
    @Override
    public boolean equals(Object o) {
        if (o instanceof map) return eq((map<K,V>)o);
        return false;
    }
    
    @Override
    public int hashCode() {
        return value.hashCode();
    }
}
