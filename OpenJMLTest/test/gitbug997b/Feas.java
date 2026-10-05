// gitbug997b: the feasibility check of fermat's precondition is nonlinear and has no model (Fermat's
// last theorem for cubes), which z3 can neither find nor refute; the check is not decided, and a
// warning names nonlinear arithmetic as the likely reason
public class Feas {
  //@ requires 0 < x <= 1000 && 0 < y <= 1000 && 0 < z <= 1000;
  //@ requires x*x*x + y*y*y == z*z*z;
  public void fermat(int x, int y, int z) {
  }
}
