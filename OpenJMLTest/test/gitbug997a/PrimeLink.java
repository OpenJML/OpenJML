// gitbug997a: a quantified % (k is not a constant) must still be instantiated from % terms outside
// the quantifier, whether their divisor is a constant (n % 2) or not (n % m)
public class PrimeLink {
  //@ requires n > 4;
  //@ requires (\forall int k; 2 <= k < n; n % k != 0);
  public static void constantDivisor(int n) {
      //@ assert n % 2 != 0;
  }

  //@ requires n > 4 && 2 <= m < n;
  //@ requires (\forall int k; 2 <= k < n; n % k != 0);
  public static void variableDivisor(int n, int m) {
      //@ assert n % m != 0;
  }

  //@ requires n > 4 && 2 <= m < n;
  //@ requires (\forall int k; 2 <= k < n; n / k * k != n);
  public static void division(int n, int m) {
      //@ assert n / m * m != n;
  }

  //@ requires n > 4;
  //@ requires (\forall int k; 2 <= k < n; n % k != 0);
  public static void wrong(int n) {
      //@ assert n % 2 == 1;
      //@ assert n % 3 == 1; // fails, e.g. for n == 11
  }
}
