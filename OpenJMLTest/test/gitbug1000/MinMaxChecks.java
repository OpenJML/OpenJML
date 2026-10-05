// Small checks of \max and \min in ESC (gitbug1000): the provable ones verify,
// the ones marked FAILS must be reported.
public class MinMaxChecks {

    //@ requires a.length == 3 && a[0] == 1 && a[1] == 7 && a[2] == 4;
    public void concrete(int[] a) {
        //@ assert (\max int i; 0 <= i < a.length; a[i]) == 7;
        //@ assert (\min int i; 0 <= i < a.length; a[i]) == 1;
    }

    //@ requires a.length == 3 && a[0] == 1L && a[1] == 7L && a[2] == 4L;
    public void concreteLong(long[] a) {
        //@ assert (\max int i; 0 <= i < a.length; a[i]) == 7L;
        //@ assert (\min int i; 0 <= i < a.length; a[i]) == 1L;
    }

    // \max and \min are not defined when no value satisfies the range (as for \choose)
    public void emptyMax() {
        //@ assert (\max int i; 0 <= i < 0; i) == 0; // FAILS: MaxNotDefined
    }

    public void emptyMin() {
        //@ assert (\min int i; 0 <= i < 0; i) == 0; // FAILS: MinNotDefined
    }

    public void maybeEmpty(int[] a) {
        //@ assert (\max int i; 0 <= i < a.length; a[i]) >= a[0]; // FAILS: MaxNotDefined, as a may be empty
    }

    // A range that is not just bounds on i: the check is (\exists int i; R; true), which the solver
    // can prove here by instantiating it at i == 1, as a[1] appears outside it
    //@ requires a.length == 3 && a[1] > 0;
    public void filtered(int[] a) {
        //@ assert (\max int i; 0 <= i < a.length && a[i] > 0; a[i]) >= a[1];
    }

    // The check applies only where the expression is evaluated
    public void guarded(int[] a) {
        //@ assert a.length == 0 || (\max int i; 0 <= i < a.length; a[i]) >= a[0];
    }

    //@ requires a.length == 3 && a[0] == 1 && a[1] == 7 && a[2] == 4;
    public void wrongMax(int[] a) {
        //@ assert (\max int i; 0 <= i < a.length; a[i]) == 4; // FAILS
    }

    //@ requires a.length == 3 && a[0] == 1 && a[1] == 7 && a[2] == 4;
    public void wrongMin(int[] a) {
        //@ assert (\min int i; 0 <= i < a.length; a[i]) == 4; // FAILS
    }
}
