// java.lang.String values, whose characters are a \string (#1043)
public class JavaStrings {

    //@ ensures \result;
    public static boolean literal() {
        String x = "abc";
        return x.length() == 3 && x.charAt(0) == 'a' && x.charAt(2) == 'c';
    }

    //@ ensures \result;
    public static boolean equal() {
        String x = "abc";
        String y = "abc";
        return x.equals(y) && !x.equals("abd") && !x.isEmpty() && "".isEmpty();
    }

    //@ requires s.length() > 0;
    //@ ensures \result == s.charAt(0);
    public static char first(String s) {
        return s.charAt(0);
    }

    //@ ensures \result;
    public static boolean starts() {
        String x = "abc";
        return x.startsWith("ab") && x.endsWith("bc") && !x.startsWith("b");
    }

    //@ ensures \result.length() == s.length() + t.length();
    public static String concat(String s, String t) {
        return s + t;
    }

    //@ ensures \result;
    public static boolean bad() {
        String x = "abc";
        return x.charAt(1) == 'c'; // fails
    }
}
