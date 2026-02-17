import java.util.*;
public class TestMap {
    
    public static void test1() {
        Integer i1 = 1;
        Object o1 = new Object();
        Integer i2 = 2;
        //@ assert i1 != null && i1 != null;
        //-RAC@ assert i1.uniqueHash != i2.uniqueHash;
        Map<Integer,Object> map = new HashMap<>();
        //@ check map.isEmpty();
        /*@ nullable */ Object o = map.get(i1);
        //@ check o == null;
        zz: o = map.get(i2);
        //@ check o == null;
        map.put(i1, o1);
        //@ check map.keys == \old(map.keys, zz).add(i1.uniqueHash);
        //@ check \forall \bigint i; i != i1.uniqueHash ; map.keys[i] == \old(map.keys, zz)[i];
        //@ check !map.isEmpty();
        o = map.get(i1);
        //@ check o == o1;
        o = map.get(i2);
        //@ check o == null;
    }
    
    public static void test2() {
        Integer i1 = 1;
        Object o1 = new Object();
        Integer i2 = 2;
        Map<Integer,Object> map = new HashMap<>();
        map.put(i1, o1);
        Set<Integer> ks = map.keySet();
        //@ check ks.size() == map.size();
        map.put(i2,o1);
        //+RAC@ check ks.size() == map.size();
        // FIXME - ESC does nt represent keySet with a modifiable backing map
    }
    
    public static void main(String... args) {
        test1();
        test2();
        //@ print "DONE";
    }
}