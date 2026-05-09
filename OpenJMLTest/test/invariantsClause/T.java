public class T {

  //@ invariants this, t;
  //@ requires true;
  public void m1(T t){}

  //@ invariants x, T; // ERROR - no x
  //@ requires true;
  public void m2(T t){}

  public int y;

  //@ invariants y;
  public void m3() {}

  //@ public normal_behavior
  //@ invariants y; // ERROR - out of place
  public void m4() {}

  //@ requires true;
  //@ invariants y; // ERROR - out of place
  public void m5() {}

}
