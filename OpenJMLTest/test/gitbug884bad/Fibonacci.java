// This is the original failing problem

public class Fibonacci {
    //@  requires n < 0;
    //@  assigns \nothing;
    //@  ensures \result == -1;
    //@ also
    //@  requires n == 0;
    //@  assigns \nothing;
    //@  ensures \result == 0;
    //@ also
    //@  requires n == 1;
    //@  assigns \nothing;
    //@  ensures \result == 1;
    //@ also
    //@  requires 2 <= n <= 47; // precomputed value, fib(47) is the largest one that does not overflow int
    //@  assigns \nothing;
    //@  ensures \result == fibCompute(n-2) + fibCompute(n-1);
    //@  measured_by n;
    //@ behaviors disjoint
    public static int fibCompute(int n) {
        if (n < 0)
            return -1;
        else if (n == 0)
            return 0;

        int[] fib = new int[n + 1];
        fib[0] = 0;
        fib[1] = 1;
        int index = 2;

        //@ maintaining 2 <= index <= fib.length;
        //@ maintaining Integer.MIN_VALUE <= fib[index-2] + fib[index-1] <= Integer.MAX_VALUE;
        //@ maintaining \forall int j; 2 <= j < index; fib[j] == fib[j - 2] + fib[j - 1];
        //@ loop_writes fib[2..n];
        //@ decreases fib.length - index;
        while (index < fib.length) {
            fib[index] = fib[index - 2] + fib[index - 1];
            index++;
        }

        return fib[n];
    }
}
