public class StaticInit {

  public static int i = 1;
  //@ public static invariant i == 0;

  public static void test() {
    i = 0;
  }

  //@ ensures i == 2;
  //@ static_initializer

  public static void main(String... args) { test(); }
}
