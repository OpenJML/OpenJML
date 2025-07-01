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
        // @ check s.length == 3; // FIXME
    }

    
    //@ spec_pure
    public static void test4() { // concat
        //@ ghost \string s1, s2;
        //@ havoc s1, s2;
        //@ ghost \string s = \string.concat(s1 , s2);
        //@ check s.size() == s1.size() + s2.size();  // FIXME - test content using substrings
    }

    //@ spec_pure
    public static void test5() { // []
        //@ ghost \string s = \string.of("ABC");
        //-RAC@ check s[1] == 'B';
        //@ check s.get(1) == 'B';
    }
    
    //@ spec_pure
    public static void test6() { // put
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.put(1,'D');
        //@ check ss.size() == 3;
        //@ check ss.get(0) == 'A' && ss.get(1) == 'D' && ss.get(2) == 'C';
    }
    
    //@ spec_pure
    public static void test7() { // insert
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.insert(1,'D');
        //@ check ss.size() == 4;
        //@ check ss.get(0) == 'A' && ss.get(1) == 'D' && ss.get(2) == 'B';
    }
    
    //@ spec_pure
    public static void test8() { // add
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.add('D');
        //@ check ss.size() == 4;
        //@ check ss.get(2) == 'C' && ss.get(3) == 'D';
        //@ check ss == \string.of("ABCD");
    }
    
    //@ spec_pure
    public static void test9() { // remove
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.remove(1);
        //@ check ss.size() == 2;
        //@ check ss.get(0) == 'A' && ss.get(1) == 'C';
        //@ check ss == \string.of("AC");
    }
    
    //@ spec_pure
    public static void test10() { // .eq
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = "ABC";
        //@ check \string.eq(s,ss);
    }
    
    public static void main(String... args) {
        test1();
        test2();
        test3();
        test4();
        test5();
        test6();
        test7();
        test8();
        test9();
        test10();
        System.out.println("END");
    }
}
