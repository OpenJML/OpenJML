/**
 * Java file with deliberate JML specification errors for diagnostics tests.
 *
 * The bad() method has a postcondition (\result < 0) that is never satisfied
 * (the method always returns a positive value), so ESC should report a
 * verification failure.  The badNull() method's requires clause applies == null
 * to a primitive (int), which is a JML type error that --check should catch.
 */
public class JmlErrors {

    /*@ requires x > 0;
      @ ensures \result < 0;
      @*/
    public int bad(int x) {
        return x;   // postcondition violated: \result is positive, not < 0
    }

    //@ requires x == null;   // type error: int cannot be null
    public int badNull(int x) {
        return x;
    }

    /*@ requires a >= 0;
      @ ensures \result >= 0;
      @*/
    public int good(int a) {
        return a;
    }
}
