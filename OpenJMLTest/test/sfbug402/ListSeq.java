import java.util.ArrayList;

public class ListSeq<E extends Object> implements Seq<E> {

    // Private Mutable State
	//@ spec_public
    private final /*@ non_null @*/ ArrayList<E> list = new ArrayList<E>(); //@ in _length;

	//@ spec_public non_null
    private Integer pos = 1; //@ in _pos;
    //@ public invariant 1 <= pos <= _length + 1;
    //@ public invariant _length < 1000;
    //@ public invariant list.size() < 1000;

    //@ represents _pos = pos;
    //@ represents _pastEnd = (pos == _length+1);
    //@ represents _length = length();
   
    // Constructor
    //@ requires elements.length < 1000;
    public ListSeq( E /*@ non_null @*/ [] elements) {
    	//@ loop_invariant list.size() == \count;
    	//@ loop_decreases elements.length - \count;
        for (E element : elements) {
            list.add(element);
        }
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
    @Override //@ pure
    public /*@ non_null */ Integer pos() {
        if (pastEnd()) throw new IndexOutOfBoundsException("There is no position past the end of the sequence.");
        return pos;
    }

    @Override //@ pure
    public E current() {
        return list.get(pos-1);
    }

    //@ also public normal_behavior
    //@   requires 0 <= list.size() < 1000;
    //@   requires 1 <= pos <= _length + 1 <= 1000;
    //@   ensures \result == list.size();
    //@ pure helper
    @Override 
    public Integer length() {
        Integer r = list.size();
        //@ show r, list.size(), _length.theInteger;
        return r;
    }

    //@ pure 
    @Override 
    public Boolean pastEnd() {
        //return pos.equals(length()+1);
        Boolean b = pos == (length()+1);
        //@ show b.theBoolean, pos.theInteger, _pos.theInteger, length().theInteger, _length.theInteger,  _pastEnd.theBoolean;
        return b;
    }
}