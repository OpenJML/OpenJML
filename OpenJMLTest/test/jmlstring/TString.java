public class TString {
    
    //@ spec_pure
    public static void test1() { // empty
        //@ ghost \string s;
        //@ assert s.isEmpty();
        //@ assert s.size() == 0;
    }
    
    //@ spec_pure
    public static void test2() { // empty
        //@ ghost \string s = \string.empty();
        //@ assert s.isEmpty();
        //@ assert s.size() == 0;
    }

    //@ spec_pure
    public static void test3() { // of, size, length
        //@ ghost \string s = \string.of("ABC");
        //@ assert s.size() == 3;
        // @ assert s.length == 3; // FIXME
    }

    
    //@ spec_pure
    public static void test4() { // concat
        //@ ghost \string s1, s2;
        //@ havoc s1, s2;
        //@ ghost \string s = \string.concat(s1 , s2);
        //@ assert s.size() == s1.size() + s2.size();  // FIXME - test content using substrings
    }

    //@ spec_pure
    public static void test5() { // []
        //@ ghost \string s = \string.of("ABC");
        //-RAC@ assert s[1] == 'B';
        //@ assert s.get(1) == 'B';
    }
    
    //@ spec_pure
    public static void test6() { // put
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.put(1,'D');
        //@ assert ss.size() == 3;
        //@ assert ss.get(0) == 'A' && ss.get(1) == 'D' && ss.get(2) == 'C';
    }
    
    //@ spec_pure
    public static void test7() { // insert
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.insert(1,'D');
        //@ assert ss.size() == 4;
        //@ assert ss.get(0) == 'A' && ss.get(1) == 'D' && ss.get(2) == 'B';
    }
    
    //@ spec_pure
    public static void test8() { // add
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.add('D');
        //@ assert ss.size() == 4;
        //@ assert ss.get(2) == 'C' && ss.get(3) == 'D';
        //@ assert \string.equals(ss,\string.of("ABCD"));
    }
    
    //@ spec_pure
    public static void test9() { // remove
        //@ ghost \string s = \string.of("ABC");
        //@ ghost \string ss = s.remove(1);
        //@ assert ss.size() == 2;
        //@ assert ss.get(0) == 'A' && ss.get(1) == 'C';
        //@ assert \string.equals(ss,\string.of("AC"));
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
        System.out.println("END");
    }
}
