// gitbug1001: ESC of \sum, \product and \num_of (a port of PR #773). Each is translated into a
// recursive SMT function over the range of its variable. The provable checks verify; the ones
// marked FAILS must be reported; the ones marked UNSUPPORTED keep the not-implemented warning.
// The arithmetic within \sum and \product is \bigint.
public class SumProductNumOf {

    //@ requires a.length == 3 && a[0] == 1 && a[1] == 2 && a[2] == 3;
    public void concrete(int[] a) {
        //@ assert (\sum int i; 0 <= i < a.length; a[i]) == 6;
        //@ assert (\product int i; 0 <= i < a.length; a[i]) == 6;
        //@ assert (\num_of int i; 0 <= i < a.length; a[i] > 1) == 2;
    }

    public void constantRanges() {
        //@ assert (\sum int i; 1 <= i <= 4; i) == 10;
        //@ assert (\product int i; 1 <= i <= 4; i) == 24;
        //@ assert (\sum int i; 0 <= i && i < 10 && i % 2 == 0; i) == 20;  // the range filters
        //@ assert (\num_of int i; 0 < i && i < 10; i % 3 == 0) == 3;
    }

    // An empty range gives the identity of the operation
    public void emptyRanges() {
        //@ assert (\sum int i; 0 <= i < 0; i) == 0;
        //@ assert (\product int i; 0 <= i < 0; i) == 1;
        //@ assert (\num_of int i; 5 <= i < 5; true) == 0;
    }

    public void longAndBigint() {
        //@ assert (\sum long i; 0 <= i < 4; i) == 6;
        //@ assert (\sum \bigint i; 0 <= i < 4; i * i) == 14;
    }

    // The inner range uses the outer variable, so the inner function takes it as a parameter
    public void nested() {
        //@ assert (\sum int i; 0 <= i < 3; (\sum int j; 0 <= j <= i; j)) == 4;
    }

    // A \let variable used in the body is likewise a parameter
    public void inLet() {
        //@ assert (\let int b = 2; (\sum int i; 0 <= i < 3; b * i)) == 6;
    }

    // A variable of the method, not bound in the expression, is used as it is
    //@ requires a.length == 3 && a[0] == 1 && a[1] == 5 && a[2] == 9 && k == 4;
    public void freeVariable(int[] a, int k) {
        //@ assert (\num_of int i; 0 <= i < a.length; a[i] > k) == 2;
    }

    // Loops that accumulate over an increasing index verify: one unfolding of the recursive
    // function relates the \sum (or \num_of) up to k+1 to the one up to k, and the invariant's
    // and the postcondition's quantifiers are the same function. (Mathematical integers, so that
    // the additions cannot overflow; and a \bigint body, as a sum of ints need not fit in an int.)
    //@ ensures \result == (\sum int i; 0 <= i < a.length; (\bigint)a[i]);
    //@ code_bigint_math spec_bigint_math
    public int sumLoop(int[] a) {
        int s = 0;
        //@ maintaining 0 <= k <= a.length && s == (\sum int i; 0 <= i < k; (\bigint)a[i]);
        //@ decreases a.length - k;
        for (int k = 0; k < a.length; k++) s += a[k];
        return s;
    }

    //@ ensures \result == (\num_of int i; 0 <= i < a.length; a[i] > 0);
    //@ code_bigint_math spec_bigint_math
    public int countLoop(int[] a) {
        int c = 0;
        //@ maintaining 0 <= k <= a.length && c == (\num_of int i; 0 <= i < k; a[i] > 0);
        //@ decreases a.length - k;
        for (int k = 0; k < a.length; k++) if (a[k] > 0) c++;
        return c;
    }

    //@ ensures \result == (\sum int i; 0 <= i < a.length; (\bigint)a[i]);
    //@ code_bigint_math spec_bigint_math
    public int whileLoop(int[] a) {
        int s = 0;
        int k = 0;
        //@ maintaining 0 <= k <= a.length && s == (\sum int i; 0 <= i < k; (\bigint)a[i]);
        //@ decreases a.length - k;
        while (k < a.length) { s += a[k]; k++; }
        return s;
    }

    // The arithmetic within \sum is \bigint; a result of a fixed-range type (the type of the body)
    // must be in that type's range, as for a cast
    public void rangeChecks() {
        //@ ghost int g = (\sum int i; 0 <= i < 2; 2000000000); // FAILS: ArithmeticCastRange
    }

    public void bigintSum() {
        //@ assert (\sum int i; 0 <= i < 2; (\bigint)2000000000) == 4000000000L;
    }

    // An inner \sum within the body of another is \bigint arithmetic, so its value (3000000000)
    // need not fit in an int; only the outer result (0, a long) is converted
    public void internalBigint() {
        //@ assert (\sum int i; 0 <= i < 2; (\sum int j; 0 <= j < 2; 1500000000) - 3000000000L) == 0;
    }

    //@ requires a.length == 3 && a[0] == 1 && a[1] == 2 && a[2] == 3;
    public void wrongSum(int[] a) {
        //@ assert (\sum int i; 0 <= i < a.length; a[i]) == 7; // FAILS
    }

    public void wrongProduct() {
        //@ assert (\product int i; 1 <= i <= 3; i) == 7; // FAILS
    }

    public void twoVariables() {
        //@ assert (\sum int i, j; 0 <= i < 2 && 0 <= j < 2; i + j) == 4; // UNSUPPORTED (two variables)
    }

    public void unbounded(int n) {
        //@ assert (\sum int i; 0 <= i; 0) == 0; // UNSUPPORTED (no upper bound)
    }
}
