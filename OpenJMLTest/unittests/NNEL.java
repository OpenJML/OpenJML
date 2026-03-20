//@ nullable_by_default
public class NNEL {

  public void m(int[] a, int[][] b, Object[] aa, Object[][] bb) {
    //@ assume \nonnullelements(a);
    //@ assume \nonnullelements(b);
    //@ assume \nonnullelements(aa);
    //@ assume \nonnullelements(bb);
  }
}
