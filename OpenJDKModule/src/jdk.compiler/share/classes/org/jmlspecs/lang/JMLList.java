package org.jmlspecs.lang;
import org.jmlspecs.annotation.*;

// FIXME - needs a real implementation for RAC
public class JMLList<E> {

    public int _size;
    
    public static class Data {}

    //@ ensures \result.size() == 0;
    @Pure @NonNull
    public JMLList<E> empty() { return null; }
    
    //@ ensures \result == _size;
    @Pure
    public int size() { return 0; }
    
//    //@ public normal_behavior
//    //@    ensures size() == \old(size()+1);
//    //@    ensures (\forall int i; i>=0 && i < \old(size()); get(i)N == \old(get(i)));
//    //@    ensures get(size()-1) == item;
//    void add(@Nullable E item);
    
    //@ ensures \result.size() == this.size() + 1;
    @Pure @NonNull
    public JMLList<E> add(@Nullable E item) { return null; }

    @Nullable @Pure
    public E get(int i) { return null; }
}
