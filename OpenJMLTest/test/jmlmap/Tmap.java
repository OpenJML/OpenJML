public class Tmap {
    
    //@ spec_pure
    public static void test1() { // empty
        Object o = new Object();
        //@ ghost \map<Object,Integer> s;
        //@ check s.isEmpty();
        //@ check s.size() == 0;
        //@ check !s.has(o);
    }
    
    //@ spec_pure
    public static void test2() { // empty
        //@ ghost var s = \map.<Object,Integer>empty();
        //@ check s.isEmpty();
        //@ check s.size() == 0;
    }

    //@ spec_pure
    public static void test3() { //putAll, remove
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
        //@ check !ssss.has(oooo);
        //@ set sss = s.remove(o);
        //@ check sss.has(oo);
        //@ check !sss.has(o);
        //@ check !sss.has(ooo);
        
    }

    //@ spec_pure
    public static void test4() {
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
        //@ check !s.has(oo);
    }

    // eq ne combine remove  m[o] = 42
    
    //@ spec_pure
    public static void test5() { // []
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \map<Object,Integer> s = \map.<Object,Integer>empty();
        //@ set s = s.put(o, 42);
        //@ check s[o] == 42;
    }
    

    public static void errors5() {
        Object[] a = new Object[5];
        //@ ghost var s = \map.<Object,Integer>empty();
        try {
            Object o = new Object();
            //@ check !s.equals(o);  // FIXME should this throw an exception or not?
        } catch (Exception e) {
            //-ESC@ set System.out.println(e);
        }
    }
    
    public static void main(String... args) {
        test1();
        test2();
        test3();
        test4();
        test5();
        errors5();
        //-ESC@ set System.out.println("END");
    }

}
