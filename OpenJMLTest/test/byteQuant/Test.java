public class Test {

  public static void m1() {
    //@ ghost byte b = (\choose byte i; -200 < i < 200; i == 150);
  }

  public static void m2() {
    //@ ghost byte b = (\choose byte i; -200 < i < 200; i == 50);
    //@ show b;
    //@ assert b != 50;
  }

  public static void m3() {
    int x = 10;
    int y = 100;
    //@ ghost byte b = (\choose byte i; x < i < y; i == 120);
  }

  public static void m4() {
    int x = 10;
    int y = 100;
    //@ ghost int b = (\choose int i; x < i < y; i == 120);
  }

  public static void main(String... args) {
      m1(); m2(); m3(); m4();
  }
}
