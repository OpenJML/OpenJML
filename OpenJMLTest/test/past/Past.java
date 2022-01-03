// This example shows that old does not propagate into a method call
// the way propoents of \past would like
public class Past {

public static class T {
  public int v;

  //@ ensures \result == (x.v == y.v);
  //@ pure
  static public boolean equals(T x, T y) { return x.v == y.v; }

}
  //@ requires t1.v == 5;
  //@ requires t2.v == 6;
  //@ requires t1 != t2;
  //@ requires t3 == t1;
  //@ requires t4 != t1 && t4 != t2 && t4 != t3 && t4.v == 5;
  static public void m(T t1, T t2, T t3, T t4) {
    t1.v = 15;
    //@ assert \old(t1).v == 15;
    //@ assert \old(t1.v) == 5;
    t2.v = 16;
    t3 = t2;
  Here: ;
    //@ assert t3.v == 16;
    //@ assert \old(t3.v) == 5;
    //@ assert \old(t3).v == 15;
    //@ assert \old(\old(t3,Here).v) == 6;

    //@ assert T.equals(t1, \old(t1));
    //@ assert T.equals(t4, \old(t1)); // This is what \past should allow

  }
}
