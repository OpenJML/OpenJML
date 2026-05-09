 @org.jmlspecs.annotation.Options("--check-feasibility=none") // tends to timeout
 public class Tmap {
    
    //@ spec_pure
    public static void test2() { // empty
        //@ ghost var s = \map.<Object,Integer>empty();
        //@ check s.isEmpty();
        //@ check s.size() == 0;
    }

    //@ spec_pure
    public static void test3() { //putAll
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        Object oooo = new Object();
        //@ ghost \map<Object,Integer> s = \map.<Object,Integer>empty().put(o,1).put(oo,2);
        //@ ghost \map<Object,Integer> ss = \map.<Object,Integer>empty().put(oo,12).put(ooo,13);
        //@ ghost \map<Object,Integer> sss = s.putAll(ss);
        //@ check (int)sss[o] == 1;
        //@ check (int)sss[oo] == 12;
        //@ check (int)sss[ooo] == 13;
        //@ check !sss.has(oooo);
        
    }

    //@ spec_pure
    public static void test3a() { //remove
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        //@ ghost \map<Object,Integer> s = \map.<Object,Integer>empty().put(o,1).put(oo,2);
        //@ ghost var sss = s.remove(o);
        //@ check sss.has(oo);
        //@ check !sss.has(o);
        //@ check !sss.has(ooo);
        
    }

    //@ spec_pure
    public static void test4() { // size after put and remove
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \map<Object,Integer> s = \map.empty();
        //@ check !s.has(oo);
        //@ set s = s.put(o, 42);
        //@ check !s.has(oo);
        //@ check s.size() == 1;
        //@ check s[o] == 42;
        //@ check s.get(o) == 42;
        //@ check s.has(o);
        //@ ghost var ss = s.remove(o);
        //@ check !ss.has(o);
        //@ check ss.size() == 0;
        //@ check ss.isEmpty();
    }

    // eq ne   m[o] = 42
    
    //@ spec_pure
    public static void test5() { // []
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \map<Object,Integer> s = \map.<Object,Integer>empty();
        //@ set s = s.put(o, 42);
        //@ check s[o] == 42;
    }
    
    public static void test6() {
        Object o = new Object();
        Object oo = new Object();
        Integer i = 42;
        //@ ghost var s = \map.<Object,Integer>empty().put(o, i);
        //@ ghost var s1 = \map.<Object,Integer>empty().put(o, i);
        //@ ghost var s2 = \map.<Object,Integer>empty().put(o, 43);
        //@ ghost var s3 = \map.<Object,Integer>empty().put(oo, i);
        //@ check s.eq(s1);
        //@ check s.equals(s1);
        //@ check s == s1;
        //@ check s != s2;
        //@ check s != s3;
        //@ check s.hashCode() == s1.hashCode();
        //-RAC@ show s, s2.toString();
    }
    
    public static void errors5() { // FIXME - rac does not show the same error as ESC?
        Object[] a = new Object[5];
        //@ ghost var s = \map.<Object,Integer>empty();
        try {
            Object o = new Object();
            //@ check !s.equals(o);
        } catch (Exception e) {
            //@ print e;
        }
    }
    
    public static class Axioms {  // FIXME - run these with RAC?
        //@ ensures ! \map.<K,V>empty().has(k) ;
        //@ model public static <K,V> void newMapIsEmpty(K k) {}
        
        //@ ensures s.put(k,v).get(k) == v;
        //@ model public static <K,V> void putGet(\map<K,V> s, K k, V v) {}
        
        //@ ensures k != kk && s.has(kk) ==> s.put(k,v).get(kk) == s.get(kk);
        //@ model public static <K,V> void putGet2(\map<K,V> s, K k, V v, K kk) {}
    }
    
    public static void main(String... args) {
        test2();
        test3();
        test3a();
        test4();
        test5();
        test6();
        errors5();
        //@ print "END";
    }

}
