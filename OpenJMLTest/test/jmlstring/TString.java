public class TString {
    // The errors are first so that the line numbers in the error messages are more stable
    //@ spec_pure
    public static void errors1() { // out of range
        //@ ghost \string s = "ABCD";
        try {
        //@ check s.get(-1) == 'A';
        } catch (StringIndexOutOfBoundsException e) {
            //+RAC@ set System.out.println(e);
        }        
    }
    //@ spec_pure
    public static void errors2() { // out of range
        //@ ghost \string s = "ABCD";
        try {
        //@ check s.get(4) == 'A';
        } catch (StringIndexOutOfBoundsException e) {
          //+RAC@ set System.out.println(e);
        }
        
    }
    //@ spec_pure
    public static void errors3() { // out of range
        //@ ghost \string s = "ABCD";
        //@ check s[-1] != 'A'; // no checking, just undefined // ERROR
        //@ check s[4] != 'A'; // no checking, just undefined // ERROR
    }
    //@ spec_pure
    public static void errors4() { // null argument
        /*@ nullable */String sn = null;
        try {
        //@ ghost \string ss = sn;
        } catch (NullPointerException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    //@ spec_pure
    public static void errors5() { // null argument
        /*@ nullable */String sn = null;
        try {
        //@ ghost \string ss = (\string)sn;
        } catch (NullPointerException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    //@ spec_pure
    public static void errors6() { // null argument
        /*@ nullable */String sn = null;
        try {
        //@ ghost \string ss = \string.of(sn);
        } catch (NullPointerException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    //@ spec_pure
    public static void errors7() { // null argument
        try {
        //@ ghost \string ss = \string.of(null);
        } catch (NullPointerException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    //@ spec_pure
    public static void errors8() { // equals
        //@ ghost \string s = "ABCD";
        try {
        //@ check s.equals("ABCD");
        } catch (RuntimeException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    
    //@ spec_pure
    public static void errors9() { // out of bounds
        //@ ghost \string s = "ABCD";
        try {
            //@ check \string.empty().head() == ' ';
        } catch (RuntimeException e) {
          //+RAC@ set System.out.println(e);
        }
        try {
            //@ check \string.empty().tail().isEmpty();
        } catch (RuntimeException e) {
          //+RAC@ set System.out.println(e);
        }
        try {
            //@ check s.head(-1).isEmpty();
        } catch (RuntimeException e) {
          //+RAC@ set System.out.println(e);
        }
        try {
            //@ check s.head(5).isEmpty();
        } catch (RuntimeException e) {
          //+RAC@ set System.out.println(e);
        }
        try {
            //@ check s.tail(-1).isEmpty();
        } catch (RuntimeException e) {
          //+RAC@ set System.out.println(e);
        }
        try {
            //@ check s.tail(5).isEmpty();
        } catch (RuntimeException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    
    //@ spec_pure
    public static void test2() { // empty
        //@ ghost \string s = \string.empty();
        //@ check s.isEmpty();
        //@ check s.length() == 0;
    }

    //@ spec_pure
    public static void test3() { // of, length
        //@ ghost \string s = \string.of("ABC");
        //@ check s.length() == 3;
        //-RAC@ check s.length == 3;
        //@ check s == \string.of("ABC");
    }

    /*-RAC@  // FIXME - reimplement this for RAC -- but it seems RAC needs length() but ESC prefers length
    //@ public normal_behavior
    //@   requires \invariant_for(s1) && \invariant_for(s2);
    //@ spec_pure
    model public static void test4(\string s1, \string s2) { // append, head, tail
        //@ check s1.length >= 0 && s2.length >= 0;
        //@ ghost \string s = s1.append(s2);
        //@ check s.length == s1.length + s2.length;
        //@ check s.length >= s1.length;
        //@ check s.substring(0,s1.length) == s1;
        //@ check s.tail(s1.length()) == s2;
        //@ check !s.isEmpty() ==> s.head(s1.length()) == s1;
        //@ check !s.isEmpty() ==> s.tail(s1.length()) == s2;
        //@ check !s.isEmpty() ==> s.tail() == s.substring(1, s.length());
        //@ check !s1.isEmpty() ==> s.head() == s1.head();
        //@ check s == s1.append(s2);
        
    }
    */

        
    public static void main(String... args) {
        test2();
        test3();
        //-RAC@ set test4("A","BC");
        //-RAC@ set test4("",\string.empty());
        errors1();
        errors2();
        errors3();
        errors4();
        errors5();
        errors6();
        errors7();
        errors8();
        errors9();
        //@ print "END";
    }
}
