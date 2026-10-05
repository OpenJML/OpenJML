// gitbug997: the same for the \bigint overload of Math.gcd
public class BigGcd {
  //@ requires x > 0 && y > 0;
  //@ ensures \result == Math.gcd((\bigint)x, (\bigint)y);
  //@ pure
  public int mygcd(int x, int y) {
      return 1; // wrong
  }
}
