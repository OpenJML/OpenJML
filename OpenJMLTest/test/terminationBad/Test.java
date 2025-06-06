public class Test {

  static public void m() {
    m();
  }

  //@ measured_by 0;
  static public void q(int i) {
    if (i > 0) q(i-1);
  }


  //@ measured_by i;
  static public void p(int i) {
    if (i > -2) p(i-1);
  }

  public static void main(String... args) {
      q(2);
      p(2);
      //m();
  }
}
