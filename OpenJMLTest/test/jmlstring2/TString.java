public class TString {

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
        test5();
        test6();
        test7();
        test8();
        test9();
        test10();
        test11();
        test12();
        misc();
        //@ print "END";
    }
}
