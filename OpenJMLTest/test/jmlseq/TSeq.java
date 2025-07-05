public class TSeq {
    
    //@ spec_pure
    public static void test1() { // empty
        //@ ghost \seq<Object> s;
        //@ assert s.isEmpty();
        //@ assert s.size() == 0;
    }
    
    //@ spec_pure
    public static void test2() { // empty
        //@ ghost var s = \seq.<Object>empty();
        //@ assert s.isEmpty();
        //@ assert s.size() == 0;
    }

    //@ spec_pure
    public static void test3() { // of, size
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \seq<Object> s = \seq.of(o,oo);
        //@ assert s.size() == 2;
    }

    
    //@ spec_pure
    /*@ model public static void test4(\seq<Object> s1,\seq<Object> s2) { // concat
        // @ ghost \seq<Object> s1, s2;
        // -RAC@ havoc s1, s2;
        //@ ghost \seq<Object> s = s1.append(s2);
        //@ show s.length, s1.length , s2.length;
        //@ assert s.length == s1.length + s2.length;
        //@ assert s.size() == s1.size() + s2.size();  // FIXME - test content using substrings
    }*/

    //@ spec_pure
    public static void test5() { // []
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \seq<Object> s = \seq.of(o,oo,o);
        //-RAC@ assert s[1] == oo;
        //@ assert s.get(1) == oo;
    }
    
    public static void main(String... args) {
        test1();
        test2();
        test3();
        //test4(); // FIXME - put back in for RAC
        test5();
        //-ESC@ set System.out.println("END");
    }

}
