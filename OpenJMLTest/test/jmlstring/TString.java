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

    /*@
    //@ public normal_behavior
    //@   requires true;
    //@ spec_pure
    model public static void test4(\string s1, \string s2) { // append, head, tail
        //@ ghost \string s = s1.append(s2);
        //@ check s.length() == s1.length() + s2.length();
        //@ check s.substring(0,s1.length()) == s1;
        //@ check s.substring(s1.length()) == s2;
        //@ check !s.isEmpty() ==> s.head(s1.length()) == s1;
        //@ check !s.isEmpty() ==> s.tail(s1.length()) == s2;
        //@ check !s.isEmpty() ==> s.tail() == s.substring(1);
        //@ check !s1.isEmpty() ==> s.head() == s1.head();
        //@ check s == s1.append(s2);
        
    }
    */

    //@ spec_pure
    public static void test5() { // [] get
        //@ ghost \string s = \string.of("ABC");
        //@ check s[1] == 'B';
        //@ check s.get(1) == 'B';
        //@ check s.head() == 'A';
        //@ check s.tail() == (\string)"BC";
    }
    
    //@ spec_pure
    public static void test6() { // put
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.put(1,'D');
        //@ check ss.length() == 3;
        //@ check ss[0] == 'A' && ss[1] == 'D' && ss[2] == 'C';
    }
    
    //@ spec_pure
    public static void test7() { // insert
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.insert(1,'D');
        //@ check ss.length() == 4;
        //@ check ss[0] == 'A' && ss[1] == 'D' && ss[2] == 'B';
    }
    
    //@ spec_pure
    public static void test8() { // append
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.append('D');
        //@ check ss.length() == 4;
        //@ check ss[2] == 'C' && ss[3] == 'D';
        //@ check ss == \string.of("ABCD");
    }
    
    //@ spec_pure
    public static void test9() { // remove
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.remove(1);
        //@ check ss.length() == 2;
        // @ check ss[0] == 'A' && ss[1] == 'C';
        //@ check ss == \string.of("AC");
    }
    
    //@ spec_pure
    public static void test10() { // .eq
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = "ABC";
        //@ check s.eq(ss);
    }
    
    //@ spec_pure
    public static void test11() { // == and cast
        //@ check (\string)"ABC" == \string.of("ABC");
    }
    
    //@ spec_pure
    public static void test12() { // == and cast
        //@ check \string.of("ACZ") == \string.of("ABC").append('Z').remove(1);
        //@ check (\string)("ACZ") == \string.of("ABC").append('Z').remove(1);
        //@ check \string.of("ABC").insert(2,'Z') == \string.of("ABZC");
        //@ check \string.of("ABCXYZ") == \string.of("ABC").append(\string.of("XYZ"));
        //@ check \string.of("ABCXYZ") == \string.of("ABC").append("XYZ");
    }
    
    //@ spec_pure
    public static void misc() { // hashCode, compareTo, equalst
        String st = "ABC";
        //@ ghost \string s = st;
        //@ ghost \string t = "ABC";
        //@ check s.hashCode() == t.hashCode();
        //-ESC@ check s.compareTo(t) == 0;
        //@ check s == t;
        //-ESC@ check t.toString().equals(st);
    }
        
    public static void main(String... args) {
        test2();
        test3();
        //@ set test4("A","BC");
        //@ set test4("",\string.empty());
        test5();
        test6();
        test7();
        test8();
        test9();
        test10();
        test11();
        test12();
        misc();
        errors1();
        errors2();
        errors3();
        errors4();
        errors5();
        errors6();
        errors7();
        errors8();
        errors9();
        System.out.println("END");
    }
}
