
public interface Seq<E extends Object> {
	
	//@ model public instance \datagroup state;
	//@ model public instance boolean _pastEnd; //@ in state;
	//@ model public instance int _pos; //@ in _pastEnd;
	//@ model public instance int _length; //@ in _pastEnd;
	
	//@ public invariant !_pastEnd ==> (1 <= _pos <= _length);


    /*@   requires !pastEnd();
      @   writes _pos;
      @   ensures !pastEnd() <==> ( pos().equals( \old(pos()) + 1) );
      @   ensures pastEnd() <==> ( \old(pos()).equals(length()) );
      @ also
      @   requires pastEnd();
      @   writes \nothing;
      @*/
    void forth();

    /*@
      @ public normal_behavior
      @   requires !_pastEnd;
      @   ensures \result == _pos;
      @*/
    /*@ spec_pure non_null @*/ Integer pos();

    /*@
      @ requires !_pastEnd;
      @*/
    /*@ spec_pure non_null @*/ E current();

    /*@ public normal_behavior
      @ ensures \result.theInteger == _length;
      @ ensures 0 <= \result;
      @*/
    /*@ spec_pure non_null helper @*/ Integer length();

    //@ public normal_behavior
    //@   ensures \result == _pastEnd;
    /*@ spec_pure non_null @*/ Boolean pastEnd();
}
