/**
 * @overview
 *
 * @author dmle
 *
 * @version
 */
public class IntMathOps {
   /*@ public normal_behavior
     @ requires y >= 0;
     @ assignable \nothing;
     @ ensures 0.0 <= \result
     @         && \result * \result <= y
     @         && ((0 <= (\result + 1) * (\result + 1))
     @            ==> y < (\result + 1) * (\result + 1));
     @*/
  public static int isqrt(int y) {
    return (int) Math.sqrt(y);
  }
}
