public class Test {

  public static void test(int i) {
    //@ split
    switch (i) {
      case 0:
        //@ assert i > 0; // FAILS
        break;
      case 1:
      default:
        //@ assert i < 0; // FAILS
    }
  }
}
