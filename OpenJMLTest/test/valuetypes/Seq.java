//import org.jmlspecs.lang.seq;

//@ pure
public class Seq<T> {
    
    //@ ensures seq.<T>empty().isEmpty();
    //@ ensures seq.<T>empty().size() == 0;
    //@ model public static <T> void newSeqIsEmpty() {}
    
    //@ ensures s.add(k).length == 1 + s.length;
    //@ model public static <T> void addBumpsSize(seq<T> s, T k) {}
    
    //@ ensures s.add(k).size() == 1 + s.size();
    //@ model public static <T> void addBumpsSize1(seq<T> s, T k) {}
    
    //@ requires 0 <= i <= s.size();
    //@ ensures s.insert(i,k).size() == 1 + s.size();
    //@ model public static <T> void addBumpsSize2(seq<T> s, T k, \bigint i) {}
    
    //@ requires 0 <= k < s.size();
    //@ ensures s.remove(k).size() == s.size() - 1;
    //@ model public static <T> void removeLowersSize(seq<T> s, int k) { show s.size(), k; }
    
    //@ public normal_behavior
    //@   requires 0 <= i <= s.size();
    //@   ensures seq.equals(s.insert(i,t).remove(i), s);
    //@ model public static <T> void addRemove(seq<T> s, T t, \bigint i) {}
    
    //@ public normal_behavior
    //@   ensures !seq.equals(s.add(t), s);
    //@ model public static <T> void addNotEqual(seq<T> s, T t) {}
    
    //@ public normal_behavior
    //@   requires 0 <= i <= s.size();
    //@   ensures !seq.equals(s.insert(i,t), s);
    //@ model public static <T> void addNotEqual1(seq<T> s, T t, \bigint i) {}
    
}
//
//class SeqTest {
//    
//    
//    //@ requires s.size() > 100;
//    /*@ model public void m(seq<\bigint> s) {
//        //@ ghost \bigint b1 = s.get(0);
//        //@ ghost \bigint b2 = s.get(0);
//        //@ assert b1 == b2;
//    }*/
//    
//    //@ requires s.size() > 100;
//    /*@ model public void mm(seq<long> s) {
//        //@ ghost long b1 = s.get(0);
//        //@ ghost long b2 = s.get(0);
//        //@ assert b1 == b2;
//    }*/
//    
//
//}