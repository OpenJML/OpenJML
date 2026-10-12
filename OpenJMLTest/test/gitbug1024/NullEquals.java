// The axioms for a method inherited from Object (here String.equals) did not include that the receiver is not
// null (#1024): Object.equals's "this == obj ==> \result" and "obj == null ==> !\result" then contradict each
// other for a null receiver and a null argument, so anything followed from a term equals(x,y) with x == y == null.
// Each check below is not provable, and is reported.
public class NullEquals {
    //@ requires (\exists String x; x == null && x.equals(null));
    public void m1() {
        //@ check false;
    }

    //@ requires (\forall String x; x == null ==> !x.equals(x));
    public void m2() {
        //@ check false;
    }

    public void m3(/*@ nullable */ String s) {
        //@ assume (\forall String x; x == s ==> x.equals(x));
        //@ check s != null;
    }
}
