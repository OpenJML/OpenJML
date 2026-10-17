// gitbug997a: a user-written gcd whose specification uses % in a quantifier. Before #997 such a
// quantifier had only arithmetic triggers and z3 instantiated it without end; now mygcd (which
// returns 1) is refuted promptly.
public class UserGcd {
  /*@ public normal_behavior
    @   requires a > 0 && b > 0;
    @   ensures \result > 0 && a % \result == 0 && b % \result == 0;
    @   ensures (\forall int c; c > 0 && a % c == 0 && b % c == 0; c <= \result);
    @ model public static pure int gcd(int a, int b);
    @*/

  //@ requires x > 0 && y > 0;
  //@ ensures \result == gcd(x, y);
  //@ pure
  public static int mygcd(int x, int y) {
      return 1; // wrong
  }
}
