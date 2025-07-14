public class TSeq {
    
    //@ spec_pure
    public static void test1() { // empty
        //@ ghost \seq<Object> s;
        //@ check s.isEmpty();
        //@ check s.length == 0;
        //@ check s.length() == 0;
    }
    
    //@ spec_pure
    public static void test2() { // empty
        //@ ghost var s = \seq.<Object>empty();
        //@ check s.isEmpty();
        //@ check s.length == 0;
        //@ check s.length() == 0;
    }

    //@ spec_pure
    public static void test3() { // of, length
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \seq<Object> s = \seq.of(o,oo);
        //-RAC@ check s.length == 2;
        //@ check s.length() == 2;
    }
    
    // FIXME - out of bounds; 

    /*@
    //@ public normal_behavior
    //@   requires true;
    //@ spec_pure
    model public static void test4(\seq<Object> s1,\seq<Object> s2) { // append, head, tail
        //@ ghost \seq<Object> s = s1.append(s2);
        //@ check s.length == s1.length + s2.length;
        //@ check s.length() == s1.length() + s2.length();
        //@ check s.head(s1.length()) == s1;
        //@ check s.tail(s1.length()) == s2;
        //@ check !s1.isEmpty() ==> s.head() == s1.head();
        //@ check s1.isEmpty() && !s2.isEmpty()==> s.head() == s2.head();
        //@ check s1.isEmpty() ==> s == s2; 
    }*/
    /*@
    //@ public normal_behavior
    //@   requires true;
    //@ spec_pure
    model public static void test4a(\seq<Object> s1,\seq<Object> s2) { // append, head, tail
        //@ ghost \seq<Object> s = s1.append(s2);
        //@ check !s.isEmpty() ==> s.tail().prepend(s.head()) == s;
        //@ check s.tail(s1.length()) == s.subseq(s1.length(), s.length());
        //@ check s.subseq(0,0).isEmpty();
        //@ check s2.prepend(s1) == s;
        //@ check s1 != s2 <==> s1.ne(s2);
        //@ check s1 == s2 <==> s1.eq(s2);
        //@ check s1 != s2 <==> !s1.eq(s2);
    }*/

    //@ spec_pure
    public static void test5() { // []
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \seq<Object> s = \seq.of(o,oo,o);
        //@ check s[1] == oo;
        //@ check s.get(1) == oo;
    }
    
    //@ spec_pure
    public static void test6() { // eq, ne, equals
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \seq<Object> s1 = \seq.of(o,oo);
        //@ ghost \seq<Object> s = \seq.of(o);
        //@ set s = s.append(oo);
        //@ check s.eq(s1);
        //@ check !s.ne(s1);
        //@ check s.equals(s1);
    }
    
    //@ spec_pure
    public static void test7() { // append, insert, remove, put
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        //@ ghost \seq<Object> s = \seq.of(o,oo);
        //@ check s.append(ooo) == \seq.<Object>of(o,oo,ooo);
        //@ check s.insert(1,ooo) == \seq.<Object>of(o,ooo,oo);
        //@ check s.insert(2,ooo) == \seq.<Object>of(o,oo,ooo);
        //@ check s.put(1,ooo) == \seq.<Object>of(o,ooo);
        //@ check s.remove(0) == \seq.<Object>of(oo);
    }
    
    //@ spec_pure
    public static void test8() { // +
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        //@ ghost \seq<Object> s = \seq.of(o,oo);
        //@ check \seq.<Object>empty().append(o) + \seq.<Object>of(oo) == s;
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
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.remove(-1);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors6() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.remove(5);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors7() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.insert(0, oo);
            //@ ghost var z = s.insert(5, oo);
            //-ESC@ set System.out.println("OK");
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors8() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.insert(-1, oo);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors9() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.insert(6, oo);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors10() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var t = \seq.<Object>empty().head();
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors11() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.head(-1);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors12() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.head(s.length()+1);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors13() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.tail(-1);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors14() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.tail(s.length()+1);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors15() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.subseq(-1,s.length());
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors16() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.subseq(0,s.length()+1);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors17() {
        Object oo = new Object();
        Object[] a = new Object[5];
        //@ ghost var s = \seq.<Object>of(a);
        try {
            //@ ghost var o = s.subseq(1,0);
        } catch (IndexOutOfBoundsException e) {
            //-ESC@ set System.out.println(e);
        }
    }
    public static void errors18() {
        Object oo = new Object();
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
        Object o = new Object();
        test1();
        test2();
        test3();
        //@ ghost var s1 = \seq.<Object>of(o,o);
        //@ ghost var s2 = \seq.<Object>of(o);
        //@ set test4(s1,s2);
        //@ set test4a(s1,s2);
        test5();
        test6();
        test7();
        test8();
        errors1();
        errors2();
        errors3();
        errors4();
        errors5();
        errors6();
        errors7();
        errors8();
        errors9();
        errors10();
        errors11();
        errors12();
        errors13();
        errors14();
        errors15();
        errors16();
        errors17();
        errors18();
        //-ESC@ set System.out.println("END");
    }

}
