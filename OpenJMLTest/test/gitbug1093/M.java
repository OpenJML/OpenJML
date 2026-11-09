import java.util.*;
// #1093: Map.jml specs of null values, frames of put/remove, the null key in clear/isEmpty
public class M {
    public void putNullVal(Map<String,Integer> map, String k) {
        map.put(k, null);
        //@ assert map.containsKey(k);
        //@ assert map.get(k) == null;
        //@ assert map.containsValue(null);
    }
    public void cvNullArg(Map<String,Integer> map) {
        boolean b = map.containsValue(null);
    }
    public void putNullKeyNullVal(Map<String,Integer> map) {
        map.put(null, null);
        //@ assert map.containsKey(null);
        //@ assert map.containsValue(null);
    }
    public void frameOtherKey(Map<String,Integer> map, String k, String j, Integer v, Integer w) {
        //@ assume k.uniqueHash != j.uniqueHash; // not !k.equals(j): see #1094
        map.put(k, v);
        map.put(j, w);
        //@ assert map.get(k) == v;
        //@ assert map.get(j) == w;
    }
    public void frameNullKey(Map<String,Integer> map, String k, Integer v, Integer w) {
        map.put(k, v);
        map.put(null, w);
        //@ assert map.get(k) == v;
        //@ assert map.get(null) == w;
    }
    public void frameNonNullKeyKeepsNullKey(Map<String,Integer> map, String k, Integer v, Integer w) {
        map.put(null, w);
        map.put(k, v);
        //@ assert map.get(null) == w;
    }
    public void removeThenGet(Map<String,Integer> map, String k) {
        map.remove(k);
        //@ assert map.get(k) == null;
        //@ assert !map.containsKey(k);
    }
    public void removeResult(Map<String,Integer> map, String k, Integer v) {
        map.put(k, v);
        /*@ nullable */ Integer r = map.remove(k);
        //@ assert r == v;
    }
    public void removeNullKey(Map<String,Integer> map, String k, Integer v) {
        map.put(k, v);
        map.remove(null);
        //@ assert !map.containsKey(null);
        //@ assert map.get(k) == v;
    }
    public void removeFrame(Map<String,Integer> map, String k, String j, Integer v) {
        //@ assume k.uniqueHash != j.uniqueHash; // not !k.equals(j): see #1094
        map.put(k, v);
        map.remove(j);
        //@ assert map.get(k) == v;
    }
    public void sizes(Map<String,Integer> map, String k, Integer v) {
        map.clear();
        //@ assert map.isEmpty() && map.size() == 0;
        //@ assert !map.containsKey(null);
        map.put(null, v);
        //@ assert map.size() == 1 && !map.isEmpty();
        map.put(k, v);
        //@ assert map.size() == 2;
        map.remove(null);
        //@ assert map.size() == 1;
    }
    public void hashMapEmpty(String k) {
        Map<String,Integer> map = new HashMap<>();
        //@ assert map.get(k) == null;
        //@ assert map.get(null) == null;
        //@ assert map.isEmpty();
    }
    public void hashMapCopy(Map<String,Integer> m, String k, Integer v) {
        m.put(k, v);
        m.put(null, v);
        HashMap<String,Integer> map = new HashMap<>(m);
        //@ assert map.get(k) == v;
        //@ assert map.get(null) == v;
        //@ assert map.size() == m.size();
    }
    public void hashMapNulls(HashMap<String,Integer> map, String k) {
        map.put(null, null);
        //@ assert map.get(null) == null;
        //@ assert map.containsKey(null) && map.containsValue(null);
        map.remove(null);
        //@ assert !map.containsKey(null);
    }
    public void abstractMapNulls(AbstractMap<String,Integer> map, String k) {
        map.put(k, null);
        //@ assert map.get(k) == null;
        //@ assert map.containsKey(k) && map.containsValue(null);
        map.remove(k);
        //@ assert !map.containsKey(k);
    }
    // Each of the following must fail; a verified one means the specs are contradictory
    public void bad1(Map<String,Integer> map, String k, Integer v) {
        map.put(k, v);
        //@ assert false;
    }
    public void bad2(Map<String,Integer> map, Integer v) {
        map.put(null, null);
        map.remove(null);
        //@ assert false;
    }
    public void bad3(Map<String,Integer> map, String k) {
        map.clear();
        map.put(k, null);
        map.remove(k);
        //@ assert false;
    }
    public void bad4() {
        Map<String,Integer> map = new HashMap<>();
        //@ assert false;
    }
}
