public class TSeq {
    
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
    
    //@ spec_pure
    public static void test9() { // equals
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \seq<Object> s1 = \seq.of(o,oo,o);
        //@ ghost \seq<Object> s2 = \seq.of(o,oo,o);
        //@ ghost \seq<Object> s3 = \seq.of(o,oo);
        //@ ghost \seq<Object> s4 = \seq.of(o,oo,oo);
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
    
    public static class Axioms {

        //@ ensures \seq.<T>empty().isEmpty();
        //@ ensures \seq.<T>empty().length == 0;
        //@ model public static <T> void newSeqIsEmpty() {}
        
        //@ requires 0 <= s.length(); // FIXME - shouldn't this be assumed by invariants on arguments
        //@ requires 0 <= ss.length(); // FIXME - shouldn't this be assumed by invariants on arguments
        //@ ensures s.append(ss).length == s.length + ss.length;
        //@ model public static <T> void appendBumpsSize(\seq<T> s, \seq<T> ss) {}
        
        //@ requires 0 <= s.length(); // FIXME - shouldn't this be assumed by invariants on arguments
        //@ ensures s.append(k).length() == 1 + s.length();
        //@ model public static <T> void appendBumpsSize1(\seq<T> s, T k) {}
        
        //@ requires 0 <= i <= s.length();
        //@ ensures s.insert(i,k).length() == 1 + s.length();
        //@ model public static <T> void insertBumpsSize2(\seq<T> s, T k, \bigint i) {}
        
        //@ requires 0 <= k < s.length();
        //@ ensures s.remove(k).length() == s.length() - 1;
        //@ model public static <T> void removeLowersLength(\seq<T> s, int k) { show s.length(), k; }
        
        //@ public normal_behavior
        //@   requires 0 <= i <= s.length();
        //@   ensures s.insert(i,t).remove(i).equals(s);
        //@ model public static <T> void insertRemove(\seq<T> s, T t, \bigint i) {}
        
        //@ public normal_behavior
        //@   requires 0 <= s.length(); // FIXME - shouldn't this be assumed by invariants on arguments
        //@   ensures !s.append(t).equals(s);
        //@ model public static <T> void appendNotEqual(\seq<T> s, T t) {}
        
        //@ public normal_behavior
        //@   requires 0 <= i <= s.length();
        //@   ensures !s.insert(i,t).equals(s);
        //@ model public static <T> void insertNotEqual1(\seq<T> s, T t, \bigint i) {}
    }
    
  //class SeqTest { // FIXME - do something with these?
//  
//  
//  //@ requires s.size() > 100;
//  /*@ model public void m(\seq<\bigint> s) {
//      //@ ghost \bigint b1 = s.get(0);
//      //@ ghost \bigint b2 = s.get(0);
//      //@ assert b1 == b2;
//  }*/
//  
//  //@ requires s.size() > 100;
//  /*@ model public void mm(\seq<long> s) {
//      //@ ghost long b1 = s.get(0);
//      //@ ghost long b2 = s.get(0);
//      //@ assert b1 == b2;
//  }*/
//  
//
//}

    
    public static void main(String... args) {
        Object o = new Object();
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
        test9();
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
