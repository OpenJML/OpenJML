public class Test3 {
    
    //@ public normal_behavior
    //@    ensures \result == \exists \bigint k; 0 <= k < s.length && k != i; s[i] == s[k];
    //@ model no_state public static boolean hasMatch(\string s, \bigint i);
    
    //@ public normal_behavior
    //@    ensures \result == \exists \bigint k; 0 <= k < j && k != i; s[i] == s[k];
    //@ model no_state public static boolean hasMatch(\string s, \bigint i, \bigint j);
    
    //@  requires s != null;
    //@  old int len = s.length();
    //@  old boolean b = \exists int i; 0 <= i < len; !hasMatch(s.chars, i);
    //@  {|
    //@  requires b;
    //@  ensures 0 <= \result < len;
    //@  ensures !hasMatch(s.chars, \result);
    //@ also
    //@   requires !b;
    //@   ensures \result == -1;
    //@  |}
    // @ behaviors disjoint;
    public static int uniqueCharS1(String s) {
        int len = s.length();
        //@ maintaining 0 <= i <= len;
        //@ maintaining \forall int j; 0 <= j < i; hasMatch(s.chars, j);
        //@ loop_writes i;
        //@ decreases len - i;
        for (int i = 0; i < len; ++i) {
            int j = 0;
            //@ maintaining 0 <= j <= len;
            //@ maintaining !hasMatch(s.chars, i, j);
            //@ loop_writes j;
            //@ decreases s.length() - j;
            while (j < len) {
                if (i != j && s.charAt(i) == s.charAt(j)) {
                    // @ assert hasMatch(s.chars, i);
                    // @ assert j < len;
                    break;
                }
                j++;
                // @ assert !hasMatch(s.chars, i, j);
            }
            if (j == len) {
                //@ assert !hasMatch(s.chars, i);
                // @ assert 0 <= i < len;
                //@ assert \exists int ii; 0 <= ii < len; !hasMatch(s.chars, ii);
                return i;
            }
            // @ assert hasMatch(s.chars, i);
            // @ assert \forall int n; 0 <= n <= i; hasMatch(s.chars, n);;
        }
        // @ assert \forall int j; 0 <= j < len; hasMatch(s.chars, j);
        // @ assert !(\exists int i; 0 <= i < len; !hasMatch(s.chars, i));
        return -1;
    }
}
