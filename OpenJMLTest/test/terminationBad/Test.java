public class Test {

  public void m() {
    m();
  }

  //@ measured_by 0;
  public void q(int i) {
    if (i > 0) q(i-1);
  }

  //@ requires i > -10;
  //@ measured_by i;
  public void p(int i) {
    if (i > -10) p(i-1);
  }

}
