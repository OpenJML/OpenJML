
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

    /*@ public normal_behavior
      @ ensures \result != null && 0 <= \result;
      @*/
    /*@ pure non_null @*/ Integer length();

    //@ public normal_behavior
    //@  ensures \result == (pos == 1 + length());
    /*@ pure non_null @*/ Boolean pastEnd();
}
