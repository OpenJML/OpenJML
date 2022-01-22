//@ nullable_by_default
public class SR {

  int k;
  SR s;
  int[] b;

  //@ requires b != null && b.length == 5;
  //@ assigns k ;
  void m1a(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ assigns t.k;
  void m1b(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ assigns a[1] ;
  void m1c(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ assigns  b[-1] ;
  void m1d(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ assigns t.*;
  void m2a(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ assigns a[*], b[*];
  void m2b(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ assigns t.s.* ;
  void m3a(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ assigns b[1..5] ;
  void m3b(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ assigns b[-1..50] ;
  void m4(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ assigns b[1..50] ;
  void m5(int[] a, SR t) {}


}
