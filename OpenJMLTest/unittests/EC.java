public class EC {

  public void m1() {}

  public void m2() {}

  public static class EInner {

    public void mi() {}

  }

  public void m3() {
    int i;
    class EL {
      public void mlocal() {}
    }
  }

  public void m4() {}

}

class EC2 {
  public void ms() {}
}
