public class A {
  //@ public normal_behavior
  //@   ensures \result >= a && \result >= b && \result >= c;
  //@   ensures \result == a || \result == b || \result == c;
  //@ implies_that public normal_behavior
  //@   ensures \result == a >= b ? (a >= c ? a : c ) : (b >= c ? b : c);
  public int max(int a, int b, int c) { 
    return (b >= c) ? (a >= b ? a : b) : (a >= c ? a : c);
  }
}
