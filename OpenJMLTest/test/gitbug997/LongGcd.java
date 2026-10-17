// gitbug997: the same for the long overload of Math.gcd
public class LongGcd {
  //@ requires x > 0 && y > 0;
  //@ ensures \result == Math.gcd(x, y);
  //@ pure
  public long mygcd(long x, long y) {
      return 1; // wrong
  }
}
