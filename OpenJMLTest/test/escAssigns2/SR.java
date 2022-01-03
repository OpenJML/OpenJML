//@ nullable_by_default
public class SR {

  int k;
  SR s;
  int[] b;

  //@ requires b != null && b.length == 5;
  //@ writes k, t.k, a[1], b[-1] ;
  void m1(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ writes t.*, a[*], b[*];
  void m2(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ writes t.s.*, b[1..5] ;
  void m3(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ writes b[-1..50] ;
  void m4(int[] a, SR t) {}

  //@ requires b != null && b.length == 5;
  //@ writes b[1..50] ;
  void m5(int[] a, SR t) {}


}
