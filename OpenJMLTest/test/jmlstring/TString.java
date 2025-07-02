public class TString {
    
    //@ spec_pure
    public static void test1() { // empty
        //@ ghost \string s;
        //@ check s.isEmpty();
        //@ check s.size() == 0;
    }
    
    //@ spec_pure
    public static void test2() { // empty
        //@ ghost \string s = \string.empty();
        //@ check s.isEmpty();
        //@ check s.size() == 0;
    }

    //@ spec_pure
    public static void test3() { // of, size, length
        //@ ghost \string s = \string.of("ABC");
        //@ check s.size() == 3;
        //@ check s.length() == 3;
        //-RAC@ check s.length == 3; // no model field for RAC -- perhaps need represents clause? FIXME
    }

    
    //@ public normal_behavior
    //@   requires true;
    //@ spec_pure
    /*@ model public static void test4(\string s1, \string s2) { // concat
        //@ ghost \string s = \string.concat(s1 , s2);
        //@ check s.size() == s1.size() + s2.size();  // FIXME - test content using substrings
    }
    @*/

    //@ spec_pure
    public static void test5() { // [] get
        //@ ghost \string s = \string.of("ABC");
        //@ check s[1] == 'B';
        // @ check s.get(1) == 'B';   // FIXME - needs fixing
    }
    
    //@ spec_pure
    public static void test6() { // put
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.put(1,'D');
        //@ check ss.size() == 3;
        //@ check ss[0] == 'A' && ss[1] == 'D' && ss[2] == 'C';
    }
    
    //@ spec_pure
    public static void test7() { // insert
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.insert(1,'D');
        //@ check ss.size() == 4;
        //@ check ss[0] == 'A' && ss[1] == 'D' && ss[2] == 'B';
    }
    
    //@ spec_pure
    public static void test8() { // add
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.add('D');
        //@ check ss.size() == 4;
        //@ check ss[2] == 'C' && ss[3] == 'D';
        //@ check ss == \string.of("ABCD");
    }
    
    //@ spec_pure
    public static void test9() { // remove
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.remove(1);
        //@ check ss.size() == 2;
        //@ check ss[0] == 'A' && ss[1] == 'C';
        //@ check ss == \string.of("AC");
    }
    
    //@ spec_pure
    public static void test10() { // .eq
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = "ABC";
        //@ check \string.eq(s,ss);
    }
    
    //@ spec_pure
    public static void test11() { // == and cast
        //@ check (\string)"ABC" == \string.of("ABC");
    }
    
    //@ spec_pure
    public static void misc() { // == and cast
        String st = "ABC";
        //@ ghost \string s = st;
        //@ ghost \string t = "ABC";
        //@ check s.hashCode() == t.hashCode();
        //@ check s.compareTo(t) == 0;
        //@ check s == t;
        //@ check t.toString().equals(st);
    }
    
    //@ spec_pure
    public static void zerrors1() { // out of range
        //@ ghost \string s = "ABCD";
        try {
        //@ check s.get(-1) == 'A';
        } catch (StringIndexOutOfBoundsException e) {
            //+RAC@ set System.out.println(e);
        }        
    }
    //@ spec_pure
    public static void zerrors2() { // out of range
        //@ ghost \string s = "ABCD";
        try {
        //@ check s.get(4) == 'A';
        } catch (StringIndexOutOfBoundsException e) {
          //+RAC@ set System.out.println(e);
        }
        
    }
    //@ spec_pure
    public static void zerrors3() { // out of range
        //@ ghost \string s = "ABCD";
        //@ check s[-1] != 'A'; // no checking, just undefined
        //@ check s[4] != 'A'; // no checking, just undefined
    }
    //@ spec_pure
    public static void zerrors4() { // null argument
        /*@ nullable */String sn = null;
        try {
        //@ ghost \string ss = sn;
        } catch (NullPointerException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    //@ spec_pure
    public static void zerrors5() { // null argument
        /*@ nullable */String sn = null;
        try {
        //@ ghost \string ss = (\string)sn;
        } catch (NullPointerException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    //@ spec_pure
    public static void zerrors6() { // null argument
        /*@ nullable */String sn = null;
        try {
        //@ ghost \string ss = \string.of(sn);
        } catch (NullPointerException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    //@ spec_pure
    public static void zerrors7() { // null argument
        try {
        //@ ghost \string ss = \string.of(null);
        } catch (NullPointerException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    //@ spec_pure
    public static void zerrors8() { // equals
        //@ ghost \string s = "ABCD";
        try {
        //@ check s.equals("ABCD");
        } catch (RuntimeException e) {
          //+RAC@ set System.out.println(e);
        }
    }
    
    public static void main(String... args) {
        test1();
        test2();
        test3();
        // @ set test4("A","BC");   // FIXME -- calling model methods crashes -- looks like a lemma
        // @ set test4("",\string.empty());
        test5();
        test6();
        test7();
        test8();
        test9();
        test10();
        test11();
        misc();
        zerrors1();
        zerrors2();
        zerrors3();
        zerrors4();
        zerrors5();
        zerrors6();
        zerrors7();
        zerrors8();
        System.out.println("END");
    }
}
