class A {
  public int k;
  //@ public invariant k >= 0;
}

public class TestInv extends A {
  public int m;
  static public int s;
  //@ public invariant m >= 0;
  //@ public static invariant s < 100;

  public void meth() {
  }

  public static void smeth() {}

  public static void main(String[] args) {
    var t = new TestInv();
    t.meth();
    System.out.println("END");
  }
}
