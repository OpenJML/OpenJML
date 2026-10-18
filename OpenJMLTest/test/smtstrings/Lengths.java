// Lengths of \string values (#1043)
public class Lengths {

    //@ model public static void literals() {
    //@   ghost \string e = "";
    //@   ghost \string s = "abc";
    //@   assert e.length() == 0;
    //@   assert e.isEmpty();
    //@   assert s.length() == 3;
    //@   assert !s.isEmpty();
    //@   assert \string.empty().length() == 0;
    //@   assert \string.empty() == e;
    //@   assert \string.of('x').length() == 1;
    //@ }

    //@ model public static void nonNegative(\string s) {
    //@   assert s.length() >= 0;
    //@   assert s.isEmpty() <==> s.length() == 0;
    //@   assert s.isEmpty() <==> s == \string.empty();
    //@ }

    //@ model public static void concat(\string s, \string t, char c) {
    //@   assert (s + t).length() == s.length() + t.length();
    //@   assert s.append(t).length() == s.length() + t.length();
    //@   assert (s + c).length() == s.length() + 1;
    //@   assert s.append(c).length() == s.length() + 1;
    //@   assert s.prepend(c).length() == s.length() + 1;
    //@   assert ((\string)"ab" + s).length() == 2 + s.length();
    //@ }

    //@ requires 0 <= i <= j <= s.length();
    //@ model public static void parts(\string s, \bigint i, \bigint j, char c) {
    //@   assert s.substring(i, j).length() == j - i;
    //@   assert s.head(i).length() == i;
    //@   assert s.tail(i).length() == s.length() - i;
    //@   assert s.insert(i, c).length() == s.length() + 1;
    //@ }

    //@ requires 0 <= i < s.length();
    //@ model public static void removePut(\string s, \bigint i, char c) {
    //@   assert s.remove(i).length() == s.length() - 1;
    //@   assert s.put(i, c).length() == s.length();
    //@   assert s.tail().length() == s.length() - 1;
    //@ }

    //@ model public static void bad1(\string s) {
    //@   assert s.length() > 0; // fails: s may be empty
    //@ }

    //@ model public static void bad2(\string s, \string t) {
    //@   assert (s + t).length() > s.length(); // fails: t may be empty
    //@ }
}
