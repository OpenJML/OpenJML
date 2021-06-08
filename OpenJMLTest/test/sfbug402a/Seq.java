
public interface Seq<E extends Object> {

    /*@ requires !pastEnd();
      @ ensures !pastEnd() ==> ( pos().equals( \old(pos()) + 1) );
      @ ensures pastEnd() <==> ( \old(pos()).equals(length()) );
      @*/
    void forth();

    /*@
      @ public normal_behavior
      @   requires !pastEnd();
      @   ensures 1 <= \result <= length();
      @*/
    /*@ pure non_null @*/ Integer pos();

    /*@
      @ requires !pastEnd();
      @*/
    /*@ non_null @*/ E current();

    /*@
      @ ensures \result != null && 0 <= \result;
      @*/
    /*@ pure non_null @*/ Integer length();

    //@ ensures !\result == (pos() <= length());
    /*@ pure non_null @*/ Boolean pastEnd();
}

// This program, AS IT STANDS, had a stack overflow crash because of the mutual recursion between pos() and pastEnd().
// The specs are fixed in sfbug402, but the specs are left non-working here to be sure the recursion problem is fixed.
