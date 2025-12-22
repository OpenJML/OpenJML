public class Super extends A {

  //@ also
  //@ ensures \result == super.m();
  //@ spec_pure
  public int m() {
    return super.m();
  }

  public static void main(String... args) {

    int k = new Super().m();
    //@ check k == 42;

  }
}

class A {
  //@ ensures \result == 42;
  //@ spec_pure
  public int m() {
    return 42;
  }
}
