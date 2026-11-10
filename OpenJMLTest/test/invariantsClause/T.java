// Type-checking of the 'invariants' method-spec clause (#651): its items are object values
// (not types or primitive values), and the clause precedes the specification cases.
public class T {

  //@ invariants this, t;
  //@ requires true;
  public void m1(T t){}

  //@ invariants x, T; // ERROR - no x; ERROR - T is a type, not a value
  //@ requires true;
  public void m2(T t){}

  public T y;
  public int k;

  //@ invariants y;
  public void m3() {}

  //@ public normal_behavior
  //@ invariants y; // ERROR - out of place
  public void m4() {}

  //@ requires true;
  //@ invariants y; // ERROR - out of place
  public void m5() {}

  //@ invariants k; // ERROR - not an object value
  public void m6() {}

}
