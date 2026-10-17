// gitbug1001b: a loop invariant with \sum that ESC does not prove: the range grows at its lower end,
// and the recursive function that translates \sum recurs on the upper end, so relating the \sum from
// k-1 to the one from k would need induction. It ends with 'Validity is unknown' (this test's timeout
// is short). Not here, because z3 sometimes proves them quickly and sometimes not within a minute: a
// \product loop (nonlinear arithmetic), and a \sum loop over lo <= i < hi with both ends symbolic.
public class LoopLimits {

    //@ ensures \result == (\sum int i; 0 <= i < a.length; (\bigint)a[i]);
    //@ code_bigint_math spec_bigint_math
    public int downLoop(int[] a) {
        int s = 0;
        //@ maintaining 0 <= k <= a.length && s == (\sum int i; k <= i < a.length; (\bigint)a[i]);
        //@ decreases k;
        for (int k = a.length; k > 0; k--) s += a[k-1];
        return s;
    }
}
