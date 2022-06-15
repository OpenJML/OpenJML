public class Test {

  public static void test(int i) {
    //@ split i > 0;
    assert i >= 0;
  }
}
