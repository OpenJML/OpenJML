// gitbug997a: the same with / in place of %
public class UserGcdDiv {
  /*@ public normal_behavior
    @   requires a > 0 && b > 0;
    @   ensures \result > 0 && (a / \result) * \result == a && (b / \result) * \result == b;
    @   ensures (\forall int c; c > 0 && (a / c) * c == a && (b / c) * c == b; c <= \result);
    @ model public static pure int gcd(int a, int b);
    @*/

  //@ requires x > 0 && y > 0;
  //@ ensures \result == gcd(x, y);
  //@ pure
  public static int mygcd(int x, int y) {
      return 1; // wrong
  }
}
