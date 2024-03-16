public class T {

  //@ requires -1000 < i < 1000;
  public static void m(int i) {
     //@ assert (\choose int x; i-1 < x && x < i+1) == i;
     //@ assert (\choose int x; i-10 < x < i-8) == i-9; // Testing a second expression with the same id
  }

  public static void mbad() {
     //@ assert (\choose int x; x >= 0) == -1; // FALSE
  }

  public static void mbad2() {
     //@ assert (\choose int x; x >= 0) == 1; // FALSE
  }

  public static void bad0() {
    //@ assert (\choose int x;; x < 0 && x > 0) == 0; // Not well-defined
  }

  public static void bad1() {
    //@ assert (\choose int x; x < 0 && x > 0) == 0; // Not well-defined
  }

  public static void bad2() {
    //@ assert (\choose int x; x < 0; x > 0) == 0; // Not well-defined
  }
}
