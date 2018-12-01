//@ pure
public class String {
    
    //@ public normal_behavior
    //@ ensures string.empty().isEmpty();
    //@ ensures string.empty().size() == 0;
    //@ model public static void newStringIsEmpty() {}
    
    //@ public normal_behavior
   //@ ensures string.string("abc").size() == 3;
    //@ model public static void newStringFromString() {}
    
    //@ public normal_behavior
    //@ ensures s.add('c').size() == 1 + s.size();
    //@ model public static void addBumpsSize(string s) {}
    
    //@ public normal_behavior
    //@ requires 0 <= i && i <= s.size();
    //@ ensures s.add(i,'c').size() == 1 + s.size();
    //@ model public static void addBumpsSize(string s, \bigint i) {}
    
    //@ public normal_behavior
    //@ requires 0 <= k && k < s.size();
    //@ ensures s.remove(k).size() == s.size() - 1;
    //@ model public static <T> void removeLowersSize(string s, int k) {}
    
    //@ public normal_behavior
    //@   requires i >= 0 && i <= s.size();
    //@   ensures string.equals(s.add(i,'c').remove(i), s);
    //@ model public static void addRemove(string s, \bigint i) { show i, s.size(); }
    
    //@ public normal_behavior
    //@   requires i >= 0 && i <= s.size();
    //@   requires 0 <= k && k < i;
    //@   ensures s.add(i,'c').get(k) == s.get(k);
    //@ model public static void addGet1(string s, \bigint i, \bigint k) { }
    
    //@ public normal_behavior
    //@   requires i >= 0 && i <= s.size();
    //@   requires i < k && k <= s.size();
    //@   ensures s.add(i,'c').get(k) == s.get(k-1);
    //@ model public static void addGet2(string s, \bigint i, \bigint k) { show i, k, s.size();  }
    
    //@ public normal_behavior
    //@   requires i >= 0 && i <= s.size();
    //@   ensures s.add(i,c).get(i) == c;
    //@ model public static void addGet(string s, \bigint i, char c) {}
    
    //@ ensures string.string("abc").get(1) == 'b';
    //@ model public static void character() {}

    
}
