public class SpecifyingLoopsExample1A {
	
    //@ ensures (\forall int j; 0 <= j <= str1.length()-1; \result.charAt(j) == str1.charAt(str1.length()-j-1));
    //@ ensures \result.length() == str1.length();
    public /*@ pure @*/ String reverseWord(String str1) {
        final int len = str1.length();
        char str2[] = new char[len];
		
        //@ maintaining 0 <= k <= len;
        //@ maintaining (\forall int j; 0 <= j < k; str2[j] == str1.charAt(len-1-j));
        //@ loop_assigns str2[*];
        //@ decreases (len-1)-k;		
        for(int k = 0; k < len; k++) {
            str2[k] = str1.charAt(len-1-k);
        }
        String res = new String(str2);
        return res;
    }

    public static void main(String [] argv) {
        final var inst = new SpecifyingLoopsExample1A();
        String tests[] = {"", "jml", "ramp", "purge", "jumpstart" };
        int failures = 0;
        //@ maintaining 0 <= i <= tests.length;
        for (int i = 0; i < tests.length; i++) {
            String teststr = tests[i];
            String tres = inst.reverseWord(teststr);
            if (!inst.isReversedIn(teststr, tres)) {
                 System.out.println("reverseWord(" + teststr +
                                   ") was wrong, it was " + tres);
                failures++;
            }
        }
        if (failures == 0) {
           System.out.println("All tests passed!");
        } else {
            System.out.println(failures + "failures :-(");
        }
    }

    //@ requires str1.length() == str2.length();
    //@ ensures \result <==> (\forall int j; 0 <= j < str1.length(); str2.charAt(j) == str1.charAt(str1.length()-1-j));
    public /*@ pure @*/ boolean isReversedIn(String str1, String str2) {
        int len = str1.length();
        //@ maintaining 0 <= k <= len;
        //@ maintaining (\forall int j; 0 <= j < k; str2.charAt(j) == str1.charAt(str1.length()-1-j));
        for (int k = 0; k < len; k++) {
            if (str2.charAt(k) != str1.charAt(len-1-k)) {
                return false;
            }
        }
        //@ assert (\forall int j; 0 <= j < str1.length(); str2.charAt(j) == str1.charAt(str1.length()-1-j));
        return true;
    }
}
