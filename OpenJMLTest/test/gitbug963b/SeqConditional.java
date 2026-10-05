// gitbug963b: a conditional expression with a \seq concatenation as a branch. The type of a
// + on \seq values was the operator's declared \seq<T>, with T unresolved; a conditional with
// such a branch took that type, and ESC declared its value with an unknown SMT sort 'T_Bound'
// ("Invalid function declaration: unknown sort 'T_Bound'"), so every proof in the class failed.
public class SeqConditional<E> {

    public void concrete(boolean b, Integer x, Integer y) {
        //@ ghost \seq<Integer> s = b ? \seq.<Integer>empty() : \seq.<Integer>of(x) + \seq.<Integer>of(y);
        //@ assert b ==> s.length() == 0;
        //@ assert !b ==> s.length() == 2;
    }

    public void generic(boolean b, E x, E y) {
        //@ ghost \seq<E> s = b ? \seq.<E>of(x) + \seq.<E>of(y) : \seq.<E>empty();
        //@ assert b ==> s.length() == 2;
    }

    public void wrong(boolean b, E x, E y) {
        //@ ghost \seq<E> s = b ? \seq.<E>empty() : \seq.<E>of(x) + \seq.<E>of(y);
        //@ assert s.length() == 2; // FAILS when b
    }
}

// The same in a represents clause, as in the original report (#963)
class Queue<E> {
    //@ public model \seq<E> q;
    /*@ spec_public nullable */ E first, second; //@ in q;
    /*@ spec_public */ boolean two; //@ in q;
    //@ private represents q = two ? \seq.<E>of(first) + \seq.<E>of(second) : \seq.<E>of(first);

    //@ requires two;
    //@ ensures \result == 2 && \result == q.length();
    //@ pure
    public int size() { return 2; }
}
