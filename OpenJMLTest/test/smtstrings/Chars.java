// Characters of \string values and conversions between char and integral types (#1043)
public class Chars {

    //@ model public static void literal() {
    //@   ghost \string s = "abc";
    //@   assert s[0] == 'a';
    //@   assert s.get(1) == 'b';
    //@   assert s.head() == 'a';
    //@   assert s[2] == 'c';
    //@   assert \string.of('x')[0] == 'x';
    //@   assert ((\string)"abc").get(1) == 'b';
    //@ }

    //@ model public static void conversions() {
    //@   ghost \string s = "abc";
    //@   assert (int)s[0] == 97;
    //@   assert s[0] + 1 == 'b';
    //@   assert (char)(s[0] + 2) == s[2];
    //@   assert s[1] - s[0] == 1;
    //@   assert s[0] < s[1];
    //@   assert (long)s[2] == 99L;
    //@   assert \string.of((char)65) == (\string)"A";
    //@ }

    //@ model public static void special() {
    //@   ghost \string s = "a\"b\\c\né￿";
    //@   assert s.length() == 8;
    //@   assert s[1] == '"';
    //@   assert s[3] == '\\';
    //@   assert s[5] == '\n';
    //@   assert s[6] == 'é';
    //@   assert s[7] == '￿';
    //@   assert (int)s[7] == 65535;
    //@ }

    //@ requires 0 <= i <= s.length();
    //@ model public static void build(\string s, \bigint i, char c) {
    //@   assert s.append(c)[s.length()] == c;
    //@   assert (s + c)[s.length()] == c;
    //@   assert s.prepend(c)[0] == c;
    //@   assert s.insert(i, c)[i] == c;
    //@ }

    //@ requires 0 <= k < i <= s.length();
    //@ model public static void unchanged(\string s, \bigint i, \bigint k, char c) {
    //@   assert s.insert(i, c)[k] == s[k];
    //@   assert s.append(c)[k] == s[k];
    //@   assert s.prepend(c)[k + 1] == s[k];
    //@ }

    //@ requires 0 <= i < k < s.length();
    //@ model public static void shifted(\string s, \bigint i, \bigint k, char c) {
    //@   assert s.insert(i, c)[k + 1] == s[k];
    //@   assert s.remove(i)[k - 1] == s[k];
    //@   assert s.put(i, c)[k] == s[k];
    //@   assert s.put(i, c)[i] == c;
    //@ }

    //@ requires 0 <= i <= j <= s.length() && i <= k < j;
    //@ model public static void substrings(\string s, \bigint i, \bigint j, \bigint k) {
    //@   assert s.substring(i, j)[k - i] == s[k];
    //@ }

    //@ model public static void bad1(\string s) {
    //@   assert s[0] == 'a'; // fails
    //@ }

    //@ model public static void bad2(\string s, \bigint i) {
    //@   ghost char c = s.get(i); // fails: precondition of get (i may be out of range)
    //@ }

    //@ model public static void bad3() {
    //@   ghost \string s = "abc";
    //@   assert s[1] == 'c'; // fails
    //@ }
}
