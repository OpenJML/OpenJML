public class PrimeChecker {
    /*@ requires n >= 2; @*/
    /*@ ensures \result <==> (\exists int k; 2 <= k && k <= 1 + n/2; n % k == 0); @*/
    /* @ ensures \result <==> (\exists int k; 2 <= k && k < n; n % k == 0); @*/
    public static boolean isNonPrime(int n) {
        if (n < 2) {
            throw new IllegalArgumentException("n must be >= 2");
        }
        boolean result = false;
        int i = 2;
        //@ ghost int nn = n/2;
        //@ maintains 2 <= i <= 1 + nn;
        //@ maintains !result;
        //@ maintains !(\exists int k; 2 <= k < i; n % k == 0);
        //@ loop_assigns i, result;
        //@ loop_decreases nn - i;
        while (i <= n / 2) {
            if (n % i == 0) {
                result = true;
                break;
            }
            i++;
        }
        //@ assert !result ==> !(\exists int k; 2 <= k < i; n % k == 0);
        //@ assert result ==> (n % i == 0);
        //@ assert !(\exists int k; nn < k < n; n%k == 0);
        return result;
    }
}
