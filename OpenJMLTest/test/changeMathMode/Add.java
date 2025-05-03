public class Add {


//@ ensures \result == x + y;
//@ pure
//@ spec_java_math code_java_math
public static int add(int x, int y) {
  return x+y;
}


//@ ensures \result == x + y; // ERROR - should fail
//@ pure
//@ spec_bigint_math code_java_math
static int add2(int x, int y) {
  return add(x,y);
}


}
