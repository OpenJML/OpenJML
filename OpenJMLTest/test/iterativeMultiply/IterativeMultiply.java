public class IterativeMultiply {

/*@
  requires x >= 0 & y >= 0;
  ensures \result == x * y;
  model public static \bigint mul(\bigint x, \bigint y) {
    \bigint a = x;
    \bigint b = y;
    \bigint c = 0;
    //@ loop_invariant a >= 0;
    //@ loop_invariant x * y == a * b + c;
    //@ loop_writes a,b,c;
    //@ loop_decreases a;
    while (a > 0) {
      if (a%2 == 1) c = c + b;
      a = a/2;
      b = b*2;
    }
    return c;
  }

  requires x >= 0 & y >= 0 & x*y <= Integer.MAX_VALUE;
  ensures \result == x * y;
  code_java_math
  model public static int mula(int x, int y) {
    int a = x;
    int b = y;
    int c = 0;
    //@ loop_invariant a >= 0 & (a > 0 ==> b >= 0) & c >= 0;
    //@ loop_invariant x * y == a * b + c;
    //@ loop_writes a,b,c;
    //@ loop_decreases a;
    while (a > 0) {
      if ((a&1) == 1) c = c + b;
      a = a/2;
      b = b*2;
    }
    return c;
  }


  requires x >= 0 & y >= 0;
  ensures \result == x * y;
  model public static \bigint mulbv(\bigint x, \bigint y) {
    \bigint a = x;
    \bigint b = y;
    \bigint c = 0;
    //@ loop_invariant a >= 0;
    //@ loop_invariant x * y == a * b + c;
    //@ loop_writes a,b,c;
    //@ loop_decreases a;
    while (a > 0) {
      if ((a%2) == 1) c = c + b; // FIXME  - implement & for \bigint
      a = a >> 1;
      b = b << 1;
    }
    return c;
  }


*/
}
