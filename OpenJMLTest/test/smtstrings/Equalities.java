// Equalities and relations users might expect of \string values (#1043)
public class Equalities {

    //@ model public static void literals() {
    //@   ghost \string s = "ab";
    //@   assert s + (\string)"c" == (\string)"abc";
    //@   assert s + 'c' == (\string)"abc";
    //@   assert (\string)"a" + (\string)"b" + (\string)"c" == (\string)"abc";
    //@   assert (\string)"abc" != (\string)"abd";
    //@   assert (\string)"abc" != (\string)"ab";
    //@   assert ((\string)"abc").eq((\string)"abc");
    //@   assert !((\string)"abc").eq((\string)"");
    //@   assert ((\string)"abc").substring(1, 3) == (\string)"bc";
    //@   assert ((\string)"abc").head(2) == (\string)"ab";
    //@   assert ((\string)"abc").tail(1) == (\string)"bc";
    //@   assert ((\string)"abc").tail() == (\string)"bc";
    //@   assert ((\string)"abc").remove(1) == (\string)"ac";
    //@   assert ((\string)"abc").insert(1, 'x') == (\string)"axbc";
    //@   assert ((\string)"abc").put(1, 'x') == (\string)"axc";
    //@   assert ((\string)"abc").prepend('x') == (\string)"xabc";
    //@   assert ((\string)"abc").startsWith("ab");
    //@   assert ((\string)"abc").endsWith("bc");
    //@   assert !((\string)"abc").startsWith("b");
    //@ }

    //@ model public static void identities(\string s, \string t, \string u) {
    //@   assert s + (\string)"" == s;
    //@   assert (\string)"" + s == s;
    //@   assert (s + t) + u == s + (t + u);
    //@   assert (s + t).startsWith(s);
    //@   assert (s + t).endsWith(t);
    //@   assert s.startsWith("");
    //@   assert s.eq(t) <==> s == t;
    //@   assert s.ne(t) <==> s != t;
    //@ }

    //@ model public static void cancellation(\string s, \string t, \string u) {
    //@   assert s + t == s + u ==> t == u;
    //@   assert t + s == u + s ==> t == u;
    //@ }

    //@ requires 0 <= i <= s.length();
    //@ model public static void split(\string s, \bigint i, char c) {
    //@   assert s.head(i) + s.tail(i) == s;
    //@   assert s.substring(0, i) + s.substring(i, s.length()) == s;
    //@   assert s.insert(i, c).remove(i) == s;
    //@ }

    //@ requires s.startsWith(t) && t.startsWith(u);
    //@ model public static void prefixTransitive(\string s, \string t, \string u) {
    //@   assert s.startsWith(u);
    //@ }

    //@ requires s.length() == t.length();
    //@ requires (\forall \bigint i; 0 <= i < s.length(); s[i] == t[i]);
    //@ model public static void extensionality(\string s, \string t) {
    //@   assert s == t;
    //@ }

    //@ model public static void bad1(\string s, \string t) {
    //@   assert s + t == t + s; // fails
    //@ }

    //@ model public static void bad2(\string s) {
    //@   assert s + (\string)"a" == (\string)"a" + s; // fails
    //@ }

    //@ model public static void bad3(\string s, \string t) {
    //@   assert s.startsWith(t) ==> s == t; // fails
    //@ }
}
