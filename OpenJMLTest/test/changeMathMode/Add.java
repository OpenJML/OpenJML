public class Add {


//@ ensures \result == x + y;
//@ spec_java_math code_java_math
public static int add(int x, int y) {
  return x+y;
}


//@ ensures \result == xx + yy; // ERROR - should fail
//@ spec_bigint_math code_java_math
static int add2(int xx, int yy) {
  return add(xx,yy);
}


}
