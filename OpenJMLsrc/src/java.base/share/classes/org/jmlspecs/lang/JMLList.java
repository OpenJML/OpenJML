package org.jmlspecs.lang;
import org.jmlspecs.annotation.*; // TODO - for now, needs for contents of .jml file

// FIXME - needs a real implementation for RAC
public class JMLList<E> {
	private JMLList() { _size = 0; }

    public int _size;
    
    public static class Data { private Data() {} }

    //@ ensures \result.size() == 0;
    /*@pure*/ /*@non_null*/
    public JMLList<E> empty() { return null; }
    
    //@ ensures \result == _size;
    /*@pure*/
    public int size() { return 0; }
    
//    //@ public normal_behavior
//    //@    ensures size() == \old(size()+1);
//    //@    ensures (\forall int i; i>=0 && i < \old(size()); get(i)N == \old(get(i)));
//    //@    ensures get(size()-1) == item;
//    void add(/*@nullable*/ E item);
    
    //@ ensures \result.size() == this.size() + 1;
    /*@pure*/ /*@non_null*/
    public JMLList<E> add(/*@nullable*/ E item) { return null; }

    /*@nullable*/ /*@pure*/
    public E get(int i) { return null; }
}
