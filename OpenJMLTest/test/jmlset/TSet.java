public class TSet {
    
    //@ spec_pure
    public static void test2() { // empty
        //@ ghost var s = \set.<Integer>empty();
        //@ check s.isEmpty();
        //@ check s.size() == 0;
        //@ check s == \set.<Integer>of();
    }

    //@ spec_pure
    public static void test3() { // of, size
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \set<Object> s = \set.of(o,oo);
        // @ check s.size() == 2;
        //@ check s.contains(o);
        //@ check s.contains(oo);
    }

    //@ spec_pure
    public static void test4() { // of, size
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \set<Object> s = \set.of(o,o);
        //@ check s.size() == 1;
        //@ check s[o];
        //@ check s.contains(o);
        //@ check !s[oo];
    }
    //@ spec_pure
    public static void test5() { // []
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \set<Object> s = \set.of(o);
        //@ check s[o];
        //@ check !s[oo];
        //@ check s.contains(o);
        //@ check !s.contains(oo);
    }
    
    //@ spec_pure
    public static void test6() { // add, remove
        Object o = new Object();
        Object oo = new Object();
        //@ ghost \set<Object> s = \set.of();
        //@ set s = s.add(o);
        //@ check s.contains(o);
        //@ check !s.contains(oo);
        //@ check !s.isEmpty();
        //@ check s.size() == 1;
        //@ set s = s.remove(o);
        //@ check !s.contains(o);
        //@ check s.size() == 0;
        //@ check s.isEmpty();
    }
    
    //@ spec_pure
    public static void test7() { // subset
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        //@ ghost \set<Object> s0 = \set.of(o);
        //@ ghost \set<Object> s1 = \set.of(o,oo);
        //@ ghost \set<Object> s2 = \set.of(o,ooo);
        //@ check s0.isSubsetOf(s2);
        //@ check s0.isProperSubsetOf(s2);
        //@ check !s1.isSubsetOf(s2);
        //@ check \set.<Object>of(o).isSubsetOf(s0);
        //@ check !\set.<Object>of(o).isProperSubsetOf(s0);
        //@ check \set.<Object>of(o) <= s0;
        //@ check !(s0 < s0);
        //@ check !(s0 < \set.<Object>of(o));
 // FIXME       //@ check !((\set.<Object>of(o)) < s0);  // FIXME - this does not parse, with or without the inner parentheses
    }
    
    //@ spec_pure
    public static void test8() { // union, intersection, subtract
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        //@ ghost \set<Object> s0 = \set.of(o);
        //@ ghost \set<Object> s1 = \set.of(o,oo);
        //@ ghost \set<Object> s2 = \set.of(o,ooo);
        //@ check s1.union(s2) == \set.<Object>of(o,oo,ooo);
        //@ check s1.intersect(s2) == s0;
        //@ check s1.subtract(s2) == \set.<Object>of(oo);
        //@ check s1.union(s2) == (s1 | s2);
        //@ check s1.intersect(s2) == (s1 & s2);
        //@ check s1.subtract(s2) == (s1 - s2);
    }
    
    //@ spec_pure
    public static void test9() { // filter
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        //@ ghost \set<Object> s0 = \set.of(o);
        //@ ghost \set<Object> s1 = \set.of(o,oo);
        //@ ghost \set<Object> s2 = \set.of(o,ooo);
//FIXME        //@ check s1.filter(x -> (x == oo)) == \set.<Object>of(oo); // These crash during code generation
//FIXME        //@ check s2.filter(x -> (x != oo)) == s2;
    }
    
    //@ spec_pure
    public static void misc() { // equals
        Object o = new Object();
        Object oo = new Object();
        Object ooo = new Object();
        //@ ghost \set<Object> s1 = \set.of(o,oo,o);
        //@ ghost \set<Object> s2 = \set.of(o,oo,o);
        //@ ghost \set<Object> s3 = \set.of(o,ooo);
        //@ ghost \set<Object> s4 = \set.of(o,oo,oo);
        //@ check s1 == s1;
        //@ check s1.equals(s1);
        //@ check s1.eq(s1);
        //@ check s1 == s2;
        //@ check s1.equals(s2);
        //@ check s1.eq(s2);
        //@ check s1 != s3;
        //@ check !s1.equals(s3);
        //@ check s1.ne(s3);
        //@ check s3.ne(s1);
        //@ check s1 == s4;
        //@ check s1.equals(s4);
        //@ check !s1.ne(s4);
        //@ check !s4.ne(s1);
        //@ check s1.hashCode() == s2.hashCode();
        //@ check !s1.equals(o);
    }
    
    public static class Axioms<T> {  // FIXME - run these with RAC?
        //@ public normal_behavior
        //@   ensures \set.<T>empty().isEmpty();
        //@ model public static <T> void newSetIsEmpty() {}
        
        //@ public normal_behavior
        //@   ensures \set.<T>empty().add(o).size() == 1;
        //@ model public static <T> void singleton(T o) {}
        
        //@ public normal_behavior
        //@   ensures !s.contains(o) ==> s.add(o).size() == 1 + s.size();
        //@ model public static <T> void addBumpsSetSize(\set<T> s, T o) {}
        
        //@ public normal_behavior
        //@   ensures s.contains(o) ==> s.add(o).size() == s.size();
        //@ model public static <T> void addDoesNotChangeSize(\set<T> s, T o) {}
        
        //@ public normal_behavior
        //@   ensures !s.contains(o) ==> s.add(o).remove(o).eq(s);
        //@ model public static <T> void addRemove(\set<T> s, T o) {}
        
        //@ public normal_behavior
        //@   ensures s.contains(o) ==> s.add(o).eq(s);
        //@ model public static <T> void addNoChange(\set<T> s, T o) {}
        
        //@ public normal_behavior
        //@   ensures !s.contains(o) ==> s.eq(s.remove(o));
        //@ model public static <T> void addRemoveA(\set<T> s, T o) {}
        
        //@ public normal_behavior
        //@   ensures s.contains(o) ==> s.remove(o).size() == s.size() - 1;
        //@ model public static <T> void addRemoveB(\set<T> s, T o) {}

    }

    public static void main(String... args) {
        test2();
        test3();
        test4();
        test5();
        test6();
        test7();
        test8();
        test9();
        misc();
        //@ print "END";
    }

}
