public class Test {

  public static void test() {
    //@ assert \key(A); // FAILS if key A is NOT DEFINED
    //@ assert !\key(A); // FAILS if key A IS DEFINED
  }
}
