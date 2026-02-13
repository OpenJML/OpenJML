public class Test {
    //@  requires s != null;
    //@  old boolean b = \exists int i; 0 <= i < s.length(); \forall int j; 0 <= j < s.length() && i != j; s.charAt(i) != s.charAt(j);
    //@ {|
    //@ requires b;
    //@  ensures 0 <= \result < s.length();
    //@  ensures \forall int i; 0 <= i < s.length() && i != \result; s.charAt(\result) != s.charAt(i);
    //@  ensures \forall int i; 0 <= i < \result; \exists int j; 0 <= j < s.length() && i != j; s.charAt(i) == s.charAt(j);   // the result is the first unique
    //@ also
    //@  requires !b;
    //@  ensures \result == -1;
    //@ |}
    //@ behaviors disjoint;
    public static int uniqueCharS1(String s) {
        //@ maintaining 0 <= i <= s.length();
        //@ maintaining \forall int j; 0 <= j < i; \exists int k; 0 <= k < s.length() && j != k; s.charAt(j) == s.charAt(k);
        //@ loop_writes i;
        //@ decreases s.length() - i;
        for (int i = 0; i < s.length(); ++i) {
            int j = 0;
            //@ maintaining 0 <= j <= s.length();
            //@ maintaining \forall int k; 0 <= k < j && k != i; s.charAt(i) != s.charAt(k);
            //@ loop_writes j;
            //@ decreases s.length() - j;
            while (j < s.length()) {
                if (i != j && s.charAt(i) == s.charAt(j))
                    break;
                j++;
            }
            if (j == s.length())
                return i;
        }
        return -1;
    }
}
