//@ model import org.jmlspecs.lang.set;

//@ pure
public class Set<T> {
    
    //@ public normal_behavior
    //@   ensures set.<T>empty().isEmpty();
    //@ model public static <T> void newSetIsEmpty() {}
    
    //@ public normal_behavior
    //@   ensures set.<T>empty().add(o).size() == 1;
    //@ model public static <T> void singleton(T o) {}
    
    //@ public normal_behavior
    //@   ensures !s.contains(o) ==> s.add(o).size() == 1 + s.size();
    //@ model public static <T> void addBumpsSetSize(set<T> s, T o) {}
    
    //@ public normal_behavior
    //@   ensures s.contains(o) ==> s.add(o).size() == s.size();
    //@ model public static <T> void addDoesNotChangeSize(set<T> s, T o) {}
    
    //@ public normal_behavior
    //@   ensures !s.contains(o) ==> s.add(o).remove(o).eq(s);
    //@ model public static <T> void addRemove(set<T> s, T o) {}
    
    //@ public normal_behavior
    //@   ensures s.contains(o) ==> s.add(o).eq(s);
    //@ model public static <T> void addNoChange(set<T> s, T o) {}
    
    //@ public normal_behavior
    //@   ensures !s.contains(o) ==> s.eq(s.remove(o));
    //@ model public static <T> void addRemoveA(set<T> s, T o) {}
    
    //@ public normal_behavior
    //@   ensures s.contains(o) ==> s.remove(o).size() == s.size() - 1;
    //@ model public static <T> void addRemoveB(set<T> s, T o) {}
    
    
    
}