// gitbug997b: warnings for quantifiers that offer the SMT solver no trigger, and for feasibility
// checks that are not decided because of nonlinear arithmetic
public class NoTrigger {
  //@ requires (\forall int i; 0 <= i < 10; i * i >= 0);  // warning: i occurs only in arithmetic
  //@ requires (\forall int i; 0 <= i < a.length; a[i] >= 0);  // no warning: a[i]
  //@ requires (\forall int c; c > 0 && n % c == 0; c <= n);  // no warning: n % c is a trigger
  //@ requires (\forall int c; c > 0; c % 2 >= 0);  // warning: c % 2 is linear arithmetic
  //@ requires (\forall int i; 0 <= i < 10; i * i >= 0 : a[i]);  // no warning: an explicit trigger
  public void m(int[] a, int n) {
  }
}
