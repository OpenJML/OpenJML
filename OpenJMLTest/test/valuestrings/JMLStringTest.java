//@ pure
public class JMLStringTest {

    public static void main(String ... args) {
        newStringIsEmpty();
        
    }
    
    //@ public normal_behavior
    //@   ensures \invariant_for(s);
    //@   ensures s.length >= 0;
    //@ model public static void stringInvariant(\string s) {}
    
    //@ public normal_behavior
    //@   ensures s[i] == s.get(i);
    //@ model public static void stringBrackets(\string s, int i) {} // FIXME - eventually change i to \bigint
    
    //@ public normal_behavior
    //@   ensures s.size() == s.length;
    //@ model public static void sizeLength(\string s) {}
    
    //@ public normal_behavior
    public static void newStringIsEmpty() {
        //@ ghost \string r = \string.empty();
        //@ assert r.isEmpty();
        //@ assert r.length == 0;
        //@ assert \invariant_for(r);
        // @ set r = (\string)("");
        // @ assert r.isEmpty();
        // @ assert r.length == 0;
        //@ assert \invariant_for(r);
    }
    
    //@ public normal_behavior
    //@ ensures ((\string)"abc").length == 3;
    //@ model public static void newStringFromString() {}
    
    //@ public normal_behavior
    //@ ensures ((\string)"").length == 0;
    //@ model public static void emptyLength() {
    //@   ghost \string s3 = "";
    //@   assert s3.length == 0;
    //@ }
    
    //@ public normal_behavior
    //@ ensures s.add('c').length == 1 + s.length;
    //@ model public static void addBumpsSize(\string s) {}
    
    //@ public normal_behavior
    //@ requires 0 <= i <= s.length;
    //@ ensures s.insert(i,'c').length == 1 + s.length;
    //@ model public static void addBumpsSize(\string s, int i) {}
    
    //@ public normal_behavior
    //@ requires 0 <= k < s.length;
    //@ ensures s.remove(k).length == s.length - 1;
    //@ model public static <T> void removeLowersSize(\string s, int k) {}
    
    //@ public normal_behavior
    //@   requires 0 <= i <= s.length;
    //@   ensures \string.eq(s.insert(i,'c').remove(i), s);
    //@ model public static void addRemove(\string s, int i) { show i, s.length; }
    
    //@ public normal_behavior
    //@   requires 0 <= k < i <= s.length;
    //@   ensures s.insert(i,'c')[k] == s[k];
    //@   ensures s.insert(i,'c').get(k) == s.get(k);
    //@ model public static void addGet1(\string s, int i, int k) { }
    
    //@ public normal_behavior
    //@   requires 0 <= i < k <= s.length;
    //@   ensures s.insert(i,'c').get(k) == s.get(k-1);
    //@ model public static void addGet2(\string s, int i, int k) { show i, k, s.length;  }
    
    //@ public normal_behavior
    //@   requires 0 <= i <= s.length;
    //@   ensures s.insert(i,c).get(i) == c;
    //@ model public static void addGet(\string s, int i, char c) {}
    
    //@ public normal_behavior
    //@   ensures ((\string)"abc").get(1) == 'b';
    //@ model public static void character() {}

    //@ public normal_behavior
    //@   ensures \string.eq(\string.empty(), \string.empty());
    //@ model public static void eq1() {}

    //@ public normal_behavior
    //@   old \string e1 = \string.empty();
    //@   old \string e2 = \string.empty();
    //@   ensures e1 == e2;
    //@   ensures \string.empty() == \string.empty();
    //@ model public static void eqOp1() {}

    //@ public normal_behavior
    //@   ensures \string.eq((\string)("abc"),(\string)("abc"));
    //@ model public static void eq2() {}

    //@ public normal_behavior
    //@   ensures !\string.eq((\string)("abc"),(\string)(""));
    //@ model public static void eq3() {}

    //@ public normal_behavior
    //@   ensures (\string)"abc" == (\string)"abc";
    //@ model public static void eqOp2() {}

    //@ public normal_behavior
    //@   ensures (\string)("abc") != (\string)("");
    //@ model public static void eqOp3() {}

    //@ public normal_behavior
    //@   ensures (\string)("abc") != (\string)("def");
    //@ model public static void eqOp4() {}

    //@ model public static void conversion1() {
    //@   ghost \string s1 = "abc";
    //@   ghost \string s2 = (\string)"abc";
    //@   ghost \string s3 = "";
    //@   assert s1 == s2;
    //@   assert s1.length == 3;
    //@   assert s3.length == 0;
    //@   assert s1 != s3;
    //@ }

    //@ model public static void conversion1a() {
    //@   ghost \string s1 = "abc";
    //@   ghost \string s2 = (\string)"abc";
    //@   ghost \string s3 = "";
    //@   assert \string.eq(s1,s2);
    //@   assert !\string.eq(s1,s3);
    //@ }

    //@ model public static void conversion2(String s) {
    //@   ghost \string s1 = s;
    //@   ghost \string s2 = (\string)s;
    //@   ghost \string s3 = (\string)(s);
    //@   assert s1 == s2;
    //@   assert s1.length == s.length();
    //@   assert s1 == s3;
    //@   assert \invariant_for((\string)s);
    //@ }

    //@ model public static void conversion2a(String s) {
    //@   ghost \string s1 = s;
    //@   ghost \string s2 = (\string)s;
    //@   ghost \string s3 = (\string)(s);
    //@   assert \string.eq(s1,s2);
    //@   assert \string.eq(s1,s3);
    //@ }

    //@ model public static void conversionBad1(nullable String s, Object o) {
    //@   ghost \string s1 = s; // verification error
    //@ }

    //@ model public static void conversionBad2(nullable String s, Object o) {
    //@   ghost \string s2 = (\string)s; // verification error
    //@ }

    //@ model public static void conversionBad3(nullable String s, Object o) {
    //@   ghost \string s3 = (\string)(s); // verification error
    //@ }


}
