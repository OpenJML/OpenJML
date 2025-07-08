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

//    //@ spec_pure
//    public static void test3() { // of, size, contains
//        Object o = new Object();
//        Object oo = new Object();
//        //@ ghost \map<Object,Integer> s = \map.of(o,oo);
//        //@ check s.size() == 2;
//        //@ check s.contains(o);
//        //@ check s.contains(oo);
//    }

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
//        test3();
        test4();
        test5();
        errors5();
        //-ESC@ set System.out.println("END");
    }

}
