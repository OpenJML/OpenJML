public class A extends B {

  //@ ghost int i;

  static class AI {}

  public static void m() {
    class C {}
    C c = new C();
  }

  //@ model void mmm();
}


class AA {
  public static void m() {}
}
