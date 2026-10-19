// The lexicographic order of \string values (#1043)
public class Order {

    //@ model public static void literals() {
    //@   assert (\string)"abc" < (\string)"abd";
    //@   assert (\string)"ab" < (\string)"abc";
    //@   assert (\string)"" < (\string)"a";
    //@   assert (\string)"b" > (\string)"abc";
    //@   assert (\string)"abc" <= (\string)"abc";
    //@   assert (\string)"abc" >= (\string)"ab";
    //@   assert ((\string)"abc").lt((\string)"b");
    //@   assert !((\string)"b").le((\string)"abc");
    //@ }

    //@ model public static void properties(\string s, \string t, \string u) {
    //@   assert !(s < s);
    //@   assert s <= s;
    //@   assert (\string)"" <= s;
    //@   assert s < t || s == t || t < s;
    //@   assert s < t ==> !(t < s);
    //@   assert s < t && t < u ==> s < u;
    //@   assert s <= t <==> !(t < s);
    //@   assert s > t <==> t < s;
    //@   assert s >= t <==> t <= s;
    //@   assert s < s + (\string)"a";
    //@ }

    //@ model public static void bad1(\string s, \string t) {
    //@   assert s <= t; // fails
    //@ }

    //@ model public static void bad2(\string s, \string t) {
    //@   assert s.length() < t.length() ==> s < t; // fails: "b" > "ab"
    //@ }
}
