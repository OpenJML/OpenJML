import java.util.*;
// #702: containsValue after put
public class T {
    public void put1(Map<String,Integer> map, String k, Integer v) {
        map.put(k, v);
        //@ assert map.containsValue(v);
    }
    public void putNullKey(Map<String,Integer> map, Integer v) {
        map.put(null, v);
        //@ assert map.containsValue(v);
    }
    public void hashMap(String k, Integer v) {
        Map<String,Integer> map = new HashMap<>();
        //@ assert !map.containsValue(v);
        map.put(k, v);
        //@ assert map.containsValue(v);
    }
    public void bad(Map<String,Integer> map, Integer v) {
        //@ assert map.containsValue(v);  // fails
    }
}
