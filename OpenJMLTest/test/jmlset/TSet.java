public class TSet {
    
    //@ spec_pure
    public static void test1() { // empty
        Object o = new Object();
        //@ ghost \set<Object> s;
        //@ check s.isEmpty();
        //@ check s.size() == 0;
        //@ check !s.contains(o);
    }
    
    //@ spec_pure
    public static void test2() { // empty
        //@ ghost var s = \set.<Object>empty();
        //@ check s.isEmpty();
        //@ check s.size() == 0;
    }

    //@ spec_pure
    public static void test3() { // of, size
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \set<Object> s = \set.of(o,oo);
        //@ check s.size() == 2;
        //@ check s.contains(o);
        //@ check s.contains(oo);
    }

    //@ spec_pure
    public static void test4() { // of, size
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \set<Object> s = \set.of(o,o);
        //@ check s.size() == 1;
        //@ check s[o];
        //@ check s.contains(o);
        //@ check !s[oo];
    }

    // add eq ne remove put isSubsetOf
    // union intersection subtract
    
    //@ spec_pure
    public static void test5() { // []
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \set<Object> s = \set.of(o);
        //@ check s[o];
        //@ check !s[oo];
        //@ check s.contains(o);
        //@ check !s.contains(oo);
    }
    

    public static void errors5() {
        Object[] a = new Object[5];
        //@ ghost var s = \set.<Object>of(a);
        try {
            Object o = new Object();
            //@ assert s.equals(o);
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
