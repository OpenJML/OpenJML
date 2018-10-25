
public class Map<K,V> {
    
    //@ ensures map.<K,V>empty().isEmpty();
    //@ ensures map.<K,V>empty().size() == 0;
    //@ model public static <K,V> void newMapIsEmpty();
    
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
    //@ pure
    //@ model public static <K,V> void putRemove(map<K,V> s, K k, V v, K kk) {}
    
    //@ public normal_behavior
    //@   requires !s.containsKey(k);
    //@   ensures !s.put(k,v).remove(k).containsKey(k);
    //@   ensures s.size() == s.put(k,v).remove(k).size();
    //@   ensures (\forall K kk; k != kk ; s.put(k,v).remove(k).containsKey(kk) == s.containsKey(kk));
    // @   ensures map.equals(s, s.put(k,v).remove(k));
    //@ pure
    //@ model public static <K,V> void putRemoveA(map<K,V> s, K k, V v) {}
//    
//    //@ ensures s.keySet().contains(k) == s.containsKey(k);
//    //@ model public static <K,V> void keyset(map<K,V> s, K k) {}
    
//    //@ ensures !s.contains(o) ==> map.equals(s, s.add(o));
//    public static <K,V> void putNoChange(map<K,V> s, T o) {}
//    
//    //@ ensures !s.contains(o) ==> map.equals(s, s.remove(o));
//    public static <K,V> void addRemove(map<K,V> s, T o) {}
//    
//    //@ ensures s.contains(o) ==> s.remove(o).size() == s.size() - 1;
//    public static <K,V> void addRemove(map<K,V> s, T o) {}
    
    
    
}