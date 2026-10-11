// --timeout-method stops a method's proof also during its feasibility checks (#1029). The proof of the check is
// easy, but the assumption is hard nonlinear arithmetic (x^3 + y^3 == z^3 has no solution in positive integers, but
// z3 cannot show it), so the first feasibility check after it runs until the method's time limit stops the solver;
// the per-query limit is large, so that is the limit that applies. The method's limit leaves ample time for the
// easy proof and the earlier feasibility checks, even on a loaded machine.
public class Feas {
    //@ requires 0 < x && 0 < y && 0 < z;
    public static void f(long x, long y, long z) {
        //@ assume x*x*x + y*y*y == z*z*z;
        long a = (x > y) ? y : z;
        //@ check a > 0;
    }
}
