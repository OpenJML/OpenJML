public class Fibonacci {
    
    //@ public normal_behavior
    //@   requires n >= 0;
    //@   ensures \result == (n == 0 ? 0 : n == 1 ? 1 : fib(n-1) + fib(n-2));
    //@   measured_by n;
    //@ model no_state static public int fib(int n);
    
    //@  requires n < 0;
    //@  assigns \nothing;
    //@  ensures \result == -1;
    //@ also
    //@  requires n >= 0;
    //@  assigns \nothing;
    //@  ensures \result == fib(n);
    //@ behaviors disjoint;
    //@ pure
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
        //@ maintaining \forall int k; 0 <= k < index; fib[k] == fib(k);
        //@ maintaining \forall int j; 2 <= j < index; fib[j] == fib[j - 2] + fib[j - 1];
        //@ loop_writes fib[2..n], index;
        //@ decreases fib.length - index;
        while (index < fib.length) {
            fib[index] = fib[index - 2] + fib[index - 1];
            index++;
        }

        return fib[n];
    }
}
