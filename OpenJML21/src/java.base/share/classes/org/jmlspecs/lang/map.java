package org.jmlspecs.lang;

import java.util.*;

//@ immutable pure non_null_by_default
public class map<K,V> implements IJmlPrimitiveType, IJmlArrayLike {
    
    private HashMap<K,V> value = new HashMap<>();
    
    public map() { value = new HashMap<K,V>(); }
    
    private map(HashMap<K,V> data) { value = data; }

    public static <KK,VV> map<KK,VV> empty() { return new map<KK,VV>(); }
    
    public V get(K k) { return value.get(k); }
    
    public boolean has(K k) { return value.containsKey(k); }
    
    public map<K,V> put(K k, V v) { 
        var c = new HashMap<K,V>(value);
        c.put(k,v);
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
