public class Assigns {

  public static class T {
    public int v;
    public int w;
  }

  public Assigns() {
    t1 = new T();
    t2 = new T();
    a = new int[10];
  }

  public T t1;
  public T t2;
  public int x;
  public int[] a;

  //@ requires t1 != t2;
  //@ requires a.length == 10;
  //@ writes \everything;
  public void m1() {
    x = 0;
    t1.v = 0;
    a[1] = 0;
  }
  //@ requires t1 != t2;
  //@ requires a.length == 10;
  //@ writes t1.v;
  public void m2() {
    x = 0; // ERROR
    t1.v = 0;
    t2.v = 0; // ERROR
    a[1] = 0; // ERROR
  }
  //@ requires t1 != t2;
  //@ requires a.length == 10;
  //@ writes a[1];
  public void m3() {
    x = 0; // ERROR
    t1.v = 0; // ERROR
    a[1] = 0;
    a[4] = 0; // ERROR
  }
  //@ requires t1 != t2;
  //@ requires a.length == 10;
  //@ writes a[*];
  public void m4() {
    x = 0; // ERROR
    t1.v = 0; // ERROR
    a[1] = 0;
    a[4] = 0;
  }
  //@ requires t1 != t2;
  //@ requires a.length == 10;
  //@ writes a[3..5];
  public void m5() {
    x = 0; // ERROR
    t1.v = 0; // ERROR
    a[4] = 0;
    a[1] = 0; // ERROR
  }
  //@ requires t1 != t2;
  //@ requires a.length == 10;
  //@ writes t1.*;
  public void m6() {
    x = 0; // ERROR
    t1.v = 0;
    a[4] = 0; // ERROR
    a[1] = 0; // ERROR
  }
  //@ requires t1 != t2;
  //@ requires a.length == 10;
  //@ writes \nothing;
  public void m7() {
    x = 0; // ERROR
    t1.v = 0; // ERROR
    a[4] = 0; // ERROR
    a[1] = 0; // ERROR
  }
}
