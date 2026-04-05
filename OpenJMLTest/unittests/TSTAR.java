public class TSTAR extends A {
  public static int k;

  // @ assigns \nothing;
  //@ assigns TSTAR.*;
  public void m() {
    k = 0;
    a = 0;
    b = 0;
  }
}

class A extends B {
  public static int a;
}

class B {
  public static int b;
}
