public class A {

  public static void main(String ... args) {
    m(0);
  }

  //@ requires i != 0;
  public static void m(int i) {}

}
