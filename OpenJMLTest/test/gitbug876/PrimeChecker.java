public class PrimeChecker {
    /*@ requires n >= 2; @*/
    /*@ ensures \result <==> (\exists int k; 2 <= k && k < n; n % k == 0); @*/
    public static boolean isNonPrime(int n) {
        if (n < 2) {
            throw new IllegalArgumentException("n must be >= 2");
        }
        boolean result = false;
        int i = 2;
        while (i <= n / 2) {
            if (n % i == 0) {
                result = true;
                break;
            }
            i++;
        }
        return result;
    }
}
