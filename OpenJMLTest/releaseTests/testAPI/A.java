public class A {

  public static void main(String... args) {
    test();
  }

  //@ ensures \result == 0;
  //@ spec_pure
  public static int test() {
    return 1;
  }
}
