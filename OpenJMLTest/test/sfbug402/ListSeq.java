import java.util.ArrayList;
// This version is fails to verify forth() but shows a bug in the positions of error messages
public class ListSeq<E extends Object> implements Seq<E> {

    // Private Mutable State
	//@ spec_public
    private final /*@ non_null @*/ ArrayList<E> list = new ArrayList<E>(); //@ in _length;
    //@ public invariant \forall int i; 0 <= i < list.size(); list.get(i) != null;

	//@ spec_public non_null
    private Integer pos = 1; //@ in _pos;
    //@ public invariant 1 <= pos <= length() + 1;
    //@ public invariant length() < 1000;
    //@ public invariant list.size() < 1000;

    //@ represents _pos = pos;
    //@ represents _pastEnd = (pos == _length+1);
    //@ represents _length = list.size();
   
    // Constructor
    //@ requires elements.length < 1000;
    //@ requires \forall int i; 0<=i<elements.length; elements[i] != null;
    public ListSeq( E /*@ non_null @*/ [] elements) {
    	//@ loop_invariant list.size() == \count;
    	//@ loop_invariant \forall int i; 0 <= i < \count; list.get(i) != null;
    	//@ loop_decreases elements.length - \count;
        for (E element : elements) {
            list.add(element);
        }
        //@ assert list.size() == elements.length;
    }

    // Interface Seq
    @Override
    public void forth() {
        if (pastEnd()) return;
        pos++;
    }

    //@ also public normal_behavior
    //@   requires !pastEnd();
    //@   ensures \result == pos;
    //@ also public exceptional_behavior
    //@   requires pastEnd();
    @Override //@ spec_pure
    public /*@ non_null */ Integer pos() {
        if (pastEnd()) throw new IndexOutOfBoundsException("There is no position past the end of the sequence.");
        return pos;
    }

    @Override //@ spec_pure
    public  /*@ non_null */ E current() {
        return list.get(pos-1);
    }

    //@ also public normal_behavior
    //@   ensures \result.theInteger == _length;
    //@ spec_pure helper
    @Override 
    public  /*@ non_null */ Integer length() {
        Integer r = list.size();
        return r;
    }

    //@ spec_pure
    @Override 
    public  /*@ non_null */ Boolean pastEnd() {
        //return pos.equals(length()+1);
        return Boolean.valueOf(pos == (length()+1));
    }
}