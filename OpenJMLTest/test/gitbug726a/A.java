import org.jmlspecs.annotation.*;
abstract public class A {

  //@ spec_pure
  abstract public int g(int i);

  //@ requires n >= 0;
  //@ ensures \result == (n == 0 ? 1 : g(f(n-1)));
  //@ measured_by n;
  @SpecPure
  public int f(int n) {
    int i = 0;
    int r = 1;
    //@ loop_invariant 0 <= i <= n;
    //@ loop_invariant r == f(i);
    //@ loop_modifies i, r;
    //@ loop_decreases n-i;
    while (i < n) {
      r = g(r);
      i++;
    }
    //@ assert r == f(n);
    return r;
  }
}
