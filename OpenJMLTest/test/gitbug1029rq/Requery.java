// A time limit reached after the first counterexample (#1029). The second check fails for an easy counterexample,
// which is reported; OpenJML then asks the solver for another failure, which needs a counterexample to the first
// check: x^3 + y^3 == z^3 has no solution in positive integers, but z3 cannot show it, so that query runs into a
// time limit. (With the easy check first, z3 does not find its counterexample quickly.) The limit that applies is
// small for the hard query but leaves ample time for the easy one, even on a loaded machine.
//   gitbug1029r:  --timeout-method=10 (the method's limit), a large per-query limit
//   gitbug1029rq: --timeout=5 (each query), no method limit
public class Requery {
    //@ requires 0 < x && 0 < y && 0 < z;
    public static void m(long x, long y, long z, int w) {
        //@ check x*x*x + y*y*y != z*z*z;
        //@ check w > 5;
    }
}
