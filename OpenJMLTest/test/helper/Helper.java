public class Helper {

  //@ public normal_behavior
  //@ helper spec_pure
  public int m() {
    return 0;
  }

}

class A extends Helper {
  public int k;
  //@ public invariant k >= 0;

  @Override
  public int m() {
    k = 0;
    return 0;
  }

  public void mm() {
     k = -1;
     int x = m();
  }
}
