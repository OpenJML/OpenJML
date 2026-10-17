// String.contains is pure and is specified as the JDK defines it, contains(s) == (indexOf(s) >= 0) for a String s,
// with a NullPointerException for null (Specs PR #26)
public class C {
    //@ requires s.contains("ab");
    //@ ensures \result;
    public static boolean m(String s) { return s.contains("ab"); }

    //@ requires s.indexOf("ab") >= 0;
    //@ ensures \result;
    public static boolean k(String s) { return s.contains("ab"); }

    //@ requires s.indexOf("ab") < 0;
    //@ ensures !\result;
    public static boolean j(String s) { return s.contains("ab"); }

    public static void n(String s) {
        try { s.contains(null); /*@ unreachable; */ } catch (NullPointerException e) {}
    }
}
