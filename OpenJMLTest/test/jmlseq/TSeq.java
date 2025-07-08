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
        //@ check s.isEmpty();
        //@ check s.size() == 0;
    }

    //@ spec_pure
    public static void test3() { // of, size
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \seq<Object> s = \seq.of(o,oo);
        //@ check s.size() == 2;
    }

    
    //@ spec_pure
    /*@ model public static void test4(\seq<Object> s1,\seq<Object> s2) { // concat
        // @ ghost \seq<Object> s1, s2;
        // -RAC@ havoc s1, s2;
        //@ ghost \seq<Object> s = s1.append(s2);
        //-RAC@ show s.length, s1.length , s2.length;
        //-RAC@ check s.length == s1.length + s2.length;
        //@ check s.size() == s1.size() + s2.size();  // FIXME - test content using substrings
    }*/

    //@ spec_pure
    public static void test5() { // []
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \seq<Object> s = \seq.of(o,oo,o);
        //@ check s[1] == oo;
        //@ check s.get(1) == oo;
    }
    
    public static void errors1() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.get(-1);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors2() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.get(5);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors3() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.put(-1, oo);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors4() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.put(5, oo);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors5() {
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
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
        //test4(); // FIXME - put back in for RAC
        test5();
        errors1();
        errors2();
        errors3();
        errors4();
        errors5();
        //-ESC@ set System.out.println("END");
    }

}
