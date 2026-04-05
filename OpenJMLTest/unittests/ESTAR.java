public class ESTAR extends A {
  public int k;
  public static int sk;

  // @ assigns \nothing;
  //@ assigns t.*;
  public void m(ESTAR t) {
    t.k = 0;
    t.a = 0;
    t.b = 0;
    ESTAR.sk = 0;
    ESTAR.sa = 0;
  }
}

class A extends B {
  public int a;
  public static int sa;
}

class B {
  public int b;
}
