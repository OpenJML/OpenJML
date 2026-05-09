package projectc;

/**
 * ESC error in ProjectC.
 * The postcondition claims the result is non-negative, but the method
 * always returns -1.  OpenJML's extended static checker (ESC) detects
 * this violation.  ProjectC has JML nature so the error should be
 * visible when ESC is run.
 */
public class EscError {
    //@ ensures \result >= 0;
    public int alwaysNegative() {
        return -1; // ESC: postcondition \result >= 0 is not satisfied
    }
}
