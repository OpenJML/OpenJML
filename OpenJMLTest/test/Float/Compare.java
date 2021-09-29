/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Float:

Float.compare(float f1, float f2)


*/


public class Compare
{
  public static void compare_finite()
  {
    //@ assert Float.compare(0.0f, 0.0f) == 0;
    //@ assert Float.compare(0.0f, 1.0f) < 0;
    //@ assert Float.compare(0.0f, -1.0f) > 0;
    //@ assert Float.compare(0.0f, Float.MAX_VALUE) < 0;
    //@ assert Float.compare(0.0f, Float.MIN_VALUE) < 0;
    //@ assert Float.compare(0.0f, -Float.MAX_VALUE) > 0;
    //@ assert Float.compare(0.0f, -Float.MIN_VALUE) > 0;
    //@ assert Float.compare(Float.MAX_VALUE, Float.MIN_VALUE) > 0;
  }

  public static void compare_infinites()
  {
    //@ assert Float.compare(0.0f, Float.POSITIVE_INFINITY) < 0;
    //@ assert Float.compare(Float.POSITIVE_INFINITY, Float.POSITIVE_INFINITY) == 0;
    //@ assert Float.compare(Float.NaN, Float.NaN) == 0;
    //@ assert Float.compare(Float.NaN, 0.0f) > 0;
    //@ assert Float.compare(Float.NaN, Float.POSITIVE_INFINITY) > 0;
    //@ assert Float.compare(Float.NEGATIVE_INFINITY, Float.NEGATIVE_INFINITY) == 0;
    //@ assert Float.compare(Float.NEGATIVE_INFINITY, 0.0f) < 0;
    //@ assert Float.compare(Float.NEGATIVE_INFINITY, Float.NaN) < 0;
  }

  public static void compare_zeros()
  {
    //@ assert Float.compare(0.0f, -0.0f) > 0;
    //@ assert Float.compare(-0.0f, 0.0f) < 0;
    //@ assert Float.compare(0.0f, 0.0f) == 0;
    //@ assert Float.compare(-0.0f, -0.0f) == 0;
  }

  //@ requires !Float.isNaN(a) && !Float.isNaN(b);
  public static void normal_properties(float a, float b)
  {
    //@ assert (a > b) ==> Float.compare(a,b) > 0;
    //@ assert (a < b) ==> Float.compare(a,b) < 0;
    //@ assert ((a == b) && (a != 0.0f)) ==> Float.compare(a,b) == 0;
    //@ assert ((Float.compare(a,0) > 0) && (Float.compare(b, a) > 0)) ==> Float.compare(b,0) > 0;
    //@ assert ((Float.compare(a,0) < 0) && (Float.compare(b, a) < 0)) ==> Float.compare(b,0) < 0;
    //@ assert ((Float.compare(0,a) > 0) && (Float.compare(a, b) > 0)) ==> Float.compare(0,b) > 0;
    //@ assert ((Float.compare(0,a) < 0) && (Float.compare(a, b) < 0)) ==> Float.compare(0,b) < 0;
  }
}
