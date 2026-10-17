// \sum in a loop invariant and a postcondition (ESC support: #1001). The \sum of int values has type int, so
// its value must fit in an int, which for an arbitrary array it need not: reported as ArithmeticCastRange.
public class Test {
  //@ ensures \result == (\sum int i; 0 <= i && i < a.length; a[i]);
  public int foo(int[] a) {
     int sum = 0;
     //@ loop_invariant 0 <= \count && \count <= a.length;
     //@ loop_invariant sum == (\sum int j; 0<=j && j<\count; a[j]);
     for (int k: a) {
        sum = sum + k;
     }
     return sum;
  }
}