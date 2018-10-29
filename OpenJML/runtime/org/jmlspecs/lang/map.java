package org.jmlspecs.lang;

import java.util.HashMap;
import java.util.Map;

//@ immutable pure
public class map<K,V> implements IJmlPrimitiveType {
    
    private Map<K,V> _map = new HashMap<K,V>();
    
    public long size() { return _map.keySet().size(); }
    
    public boolean containsKey(K k) { return _map.keySet().contains(k); }

    public V get(K k) { return _map.get(k); }

    public boolean isEmpty() { return size() == 0; }
    
    static public <K,V> map<K,V> empty() { return new map<K,V>(); }
    
    public static <K,V> boolean equals(map<K,V> s, map<K,V> ss) { return true; } // FIXME
    
    public boolean equals(map<K,V> s) { return this == s || equals(this,s); }
    
    public map<K,V> put(K k, V v) { map<K,V> newmap = new map<>(); newmap._map.put(k,v); return newmap; }
    
    public map<K,V> remove(K k) { return this; } // FIXME
    
//    public normal_behavior
//      ensures (\forall K k;; \result.contains(k) <==> this.containsKey(k));
//    model public set<K> keySet();

}

