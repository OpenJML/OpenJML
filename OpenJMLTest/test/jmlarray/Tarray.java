public class Tarray {

    public static void errors1() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \array.<Object>of(a);
        try {
            //@ ghost var o = s.get(-1);
        } catch (ArrayIndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors2() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \array.<Object>of(a);
        try {
            //@ ghost var o = s.get(5);
        } catch (ArrayIndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors3() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \array.<Object>of(a);
        try {
            //@ ghost var o = s.put(-1, oo);
        } catch (ArrayIndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors4() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \array.<Object>of(a);
        try {
            //@ ghost var o = s.put(5, oo);
        } catch (ArrayIndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors5() {
        Object[] a = new Object[5];
        //@ ghost var s = \array.<Object>of(a);
        try {
            Object o = new Object();
            //@ assert s.equals(o);
        } catch (Exception e) {
            //-ESC@ set System.out.println(e);
        }
    }

    //@ spec_pure
    public static void test2() { // empty
        //@ ghost var s = \array.<Object>empty();
        //@ check s.length == \bigint.zero;
    }

    //@ spec_pure
    public static void test3() { // of, length
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \array<Object> s = \array.of(o,oo);
        //@ check s.length == \bigint.of(2);
        //@ check \array.<Integer>of().length == 0;
        //@ ghost var a = \array.<Integer>empty();
        //@ ghost var b = \array.<Integer>of();
        //@ check a.length == b.length;
        //@ check a.eq(b);
        //-RAC@ check \forall \bigint i;; a[i] == b[i];
        //@ check \array.<Integer>empty() == \array.<Integer>of();
    }
    
    //@ spec_pure
    public static void test4() { // of, length
        Object[] o = new Object[4];
        //@ ghost \array<Object> s = \array.of(o);
        //@ check s.length == 4;
        //@ set s = \array.of();
        //@ check s.length == 0;
    }
    
    //@ spec_pure
    public static void test5() { // []
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \array<Object> s = \array.of(o,oo,o);
        //@ check s.length == 3;
        //@ check s[1] == oo;
        //@ check s.get(1) == oo;
    }
    
    //@ spec_pure
    public static void test6() { // put
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        //@ ghost \array<Object> s = \array.of(o,oo,o);
        //@ check s[1] == oo;
        //@ ghost var ss = s.put(1,ooo);
        //@ check s.get(1) == oo;
        //@ check ss.get(1) == ooo;
    }
    
//    public static void test6a(int i, Object o, Object oo) {
//        //@ assume o != oo;
//        //@ ghost \bigint ii = i; set ii = ii*2;
//        //@ ghost \array<Object> a; havoc a;
//        //@ set a = a.put(ii,oo);
//        //@ ghost \array<Object> b = a;
//        //@ set a = a.put(ii,o);
//        //@ check a[ii+1] == b[ii+1];
//        //@ check a[ii] == o;
//        //@ check b[ii] == oo;
//    }

    //@ spec_pure
    public static void test7() { // equals
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \array<Object> s1 = \array.of(o,oo,o);
        //@ ghost \array<Object> s2 = \array.of(o,oo,o);
        //@ ghost \array<Object> s3 = \array.of(o,oo);
        //@ ghost \array<Object> s4 = \array.of(o,oo,oo);
        //@ check s1 == s1;
        //@ check s1.equals(s1);
        //@ check s1.eq(s1);
        //@ check s1 == s2;
        //@ check s1.equals(s2);
        //@ check s1.eq(s2);
        //@ check s1 != s3;
        //@ check !s1.equals(s3);
        //@ check s1.ne(s3);
        //@ check s3.ne(s1);
        //@ check s1 != s4;
        //@ check !s1.equals(s4);
        //@ check s1.ne(s4);
        //@ check s4.ne(s1);
        //@ check s1.hashCode() == s2.hashCode();
    }
    
    //@ spec_pure
    public static void test8() { // equality
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        //@ ghost \array<Object> s1 = \array.of(o,oo,o);
        //@ ghost \array<Object> s2 = \array.of(o,oo,o);
        //@ ghost \array<Object> s3 = \array.of(o,o,o);
        //@ ghost \array<Object> s4 = \array.of(o,oo);
        //@ check s1 == s1;
        //@ check s1 == s2;
        //@ check s1 != s3;
        //@ check s1 != s4;
        //@ check s1.eq(s1);
        //@ check s1.eq(s2);
        //@ check s1.ne(s3);
        //@ check s1.ne(s4);
    }
        
    //@ spec_pure
    public static void test9() { // equality
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        //@ ghost \array<Object> s1 = \array.of(o,oo,o);
        //@ check \array.<Object>empty() != s1;
        //@ check \array.<Object>empty() == \array.<Object>empty();
        //@ check \array.<Object>empty().ne(s1);
        //@ check \array.<Object>empty().eq(\array.<Object>empty());
    }
        
    public static void main(String... args) {
        //@ print "START";
        test2();
        test3();
        test5();
        test6();
        Object o = new Object(); Object oo = new Object();
        // -RAC@ set test6a(0, o, oo);
        test7();
        test8();
        test9();
        errors1();
        errors2();
        errors3();
        errors4();
        errors5();
        //@ print "END";
    }

}
