//@ pure
public class Map<K,V> {
    
    //@ ensures new java.util.Map<K,V>().isEmpty();
    //@ ensures new java.util.Map<K,V>().size() == 0;
    //@ model public static <K,V> void newMapIsEmpty() {}
    
    //@ ensures !s.containsKey(k) ==> s.put(k,v).size() == 1 + s.size();
    //@ model public static <K,V> void putBumpsSize(map<K,V> s, K k, V v) {}
    
    //@ ensures s.containsKey(k) ==> s.put(k,v).size() == s.size();
    //@ model public static <K,V> void putDoesNotChangeSize(map<K,V> s, K k, V v) {}
    
    //@ public normal_behavior
    //@   requires !s.containsKey(k);
    //@   requires k != kk;
    //@   ensures !s.put(k,v).remove(k).containsKey(k);
    //@   ensures s.size() == s.put(k,v).remove(k).size();
    //@   ensures s.put(k,v).remove(k).containsKey(kk) == s.containsKey(kk);
    //@   ensures map.equals(s, s.put(k,v).remove(k));
    //@ model public static <K,V> void putRemove(map<K,V> s, K k, V v, K kk) {}
    
    //@ public normal_behavior
    //@   requires !s.containsKey(k);
    //@   ensures !s.put(k,v).remove(k).containsKey(k);
    //@   ensures s.size() == s.put(k,v).remove(k).size();
    //@   ensures (\forall K kk; k != kk ; s.put(k,v).remove(k).containsKey(kk) == s.containsKey(kk));
    //@   ensures map.equals(s, s.put(k,v).remove(k));
    //@ model public static <K,V> void putRemoveA(map<K,V> s, K k, V v) {}
    
    //@ public normal_behavior
    //@   ensures s.keySet().contains(k) == s.containsKey(k);
    //@ model public static <K,V> void keyset(map<K,V> s, K k) {}
    
    //@ public normal_behavior
    //@   ensures s.containsKey(k) ==> map.equals(s, s.put(k,s.get(k)));
    //@ model public static <K,V> void putNoChange(map<K,V> s, K k) {}
    
    //@ public normal_behavior
    //@   ensures !s.containsKey(k) ==> (s == s.remove(k));
    //@ model public static <K,V> void addRemove(map<K,V> s, K k) {}
    
    //@ public normal_behavior
    //@   ensures s.containsKey(o) ==> s.remove(o).size() == s.size() - 1;
    //@ model public static <K,V> void addRemoveB(map<K,V> s, K o) {}
    
    
    
}