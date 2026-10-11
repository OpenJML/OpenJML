// The two kinds of time limit (#1029). The check below is hard nonlinear arithmetic: x^3 + y^3 == z^3 has no
// solution in positive integers, but z3 cannot show it, so the query always runs into a time limit. Each test sets
// one limit small and the other large, so which limit stops the query does not depend on the machine's speed.
//   gitbug1029:  --timeout=1 (each solver query), no method limit
//   gitbug1029m: --timeout-method=1 (the solver's total time for the method), a large per-query limit
public class Timeouts {
    //@ requires 0 < x && 0 < y && 0 < z;
    public static void m(long x, long y, long z) {
        //@ check x*x*x + y*y*y != z*z*z;
    }
}
