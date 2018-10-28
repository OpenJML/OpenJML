//@ model import org.jmlspecs.lang.set;

public class Set<T> {
    
    //@ ensures set.<T>set().empty();
    //@ model public static <T> void newSetIsEmpty() {}
    
    //@ ensures set.<T>set().add(o).size() == 1;
    //@ model public static <T> void singleton(T o) {}
    
    //@ ensures !s.contains(o) ==> s.add(o).size() == 1 + s.size();
    //@ model public static <T> void addBumpsSize(set<T> s, T o) {}
    
    //@ ensures s.contains(o) ==> s.add(o).size() == s.size();
    //@ model public static <T> void addDoesNotChangeSize(set<T> s, T o) {}
    
    //@ ensures !s.contains(o) ==> set.equals(s.add(o).remove(o), s);
    //@ model public static <T> void addRemove(set<T> s, T o) {}
    
    //@ ensures s.contains(o) ==> set.equals(s.add(o), s);
    //@ model public static <T> void addNoChange(set<T> s, T o) {}
    
    //@ ensures !s.contains(o) ==> set.equals(s, s.remove(o));
    //@ model public static <T> void addRemoveA(set<T> s, T o) {}
    
    //@ ensures s.contains(o) ==> s.remove(o).size() == s.size() - 1;
    //@ model public static <T> void addRemoveB(set<T> s, T o) {}
    
    
    
}