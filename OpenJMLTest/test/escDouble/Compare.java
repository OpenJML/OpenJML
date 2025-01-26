/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Double:

Double.compare(double d1, double d2)


*/


public class Compare
{
  // hangs
  public static void compare_finite()
  {
    //@ assert Double.compare(0.0, 0.0) == 0;
    //@ assert Double.compare(0.0, 1.0) < 0;
    //@ assert Double.compare(0.0, -1.0) > 0;
    //@ assert Double.compare(0.0, Double.MAX_VALUE) < 0;
    //@ assert Double.compare(0.0, Double.MIN_VALUE) < 0;
    //@ assert Double.compare(0.0, -Double.MAX_VALUE) > 0;
    //@ assert Double.compare(0.0, -Double.MIN_VALUE) > 0;
    //@ assert Double.compare(Double.MAX_VALUE, Double.MIN_VALUE) > 0;
  }

  // fails to verify
  public static void compare_infinites()
  {
    //@ assert Double.compare(0.0, Double.POSITIVE_INFINITY) < 0;
    //@ assert Double.compare(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY) == 0;
    //@ assert Double.compare(Double.NaN, Double.NaN) == 0;
    //@ assert Double.compare(Double.NaN, 0.0) > 0;
    //@ assert Double.compare(Double.NaN, Double.POSITIVE_INFINITY) > 0;
    //@ assert Double.compare(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY) == 0;
    //@ assert Double.compare(Double.NEGATIVE_INFINITY, 0.0) < 0;
    //@ assert Double.compare(Double.NEGATIVE_INFINITY, Double.NaN) < 0;
  }

  // fails to verify
  public static void compare_zeros()
  {
    //@ assert Double.compare(0.0, -0.0) > 0;
    //@ assert Double.compare(-0.0, 0.0) < 0;
    //@ assert Double.compare(0.0, 0.0) == 0;
    //@ assert Double.compare(-0.0, -0.0) == 0;
  }

  //@ requires !Double.isNaN(a) && !Double.isNaN(b);
  //test with limited range && a > 0.0 && b > 0.0 && a < 1.0 && b < 1.0;
  public static void normal_properties(double a, double b)
  {
    // @ show a,b;
    //@ assert (a > b) ==> Double.compare(a,b) > 0;
    //@ assert (a < b) ==> Double.compare(a,b) < 0;
    //@ assert ((a == b) && (a != 0.0)) ==> Double.compare(a,b) == 0;
    //@ assert ((Double.compare(a,0) > 0) && (Double.compare(b, a) > 0)) ==> Double.compare(b,0) > 0;
    //@ assert ((Double.compare(a,0) < 0) && (Double.compare(b, a) < 0)) ==> Double.compare(b,0) < 0;
    //@ assert ((Double.compare(0,a) > 0) && (Double.compare(a, b) > 0)) ==> Double.compare(0,b) > 0;
    //@ assert ((Double.compare(0,a) < 0) && (Double.compare(a, b) < 0)) ==> Double.compare(0,b) < 0;
  }

  //MAX_VALUE checks cause indefinite hangs
  public static void special_properties(double a, double b)
  {
    //@ assert (Double.isNaN(a) && Double.isNaN(b)) ==> Double.compare(a,b) == 0;
    //@ assert (Double.isNaN(a) && (b == Double.POSITIVE_INFINITY)) ==> Double.compare(a,b) > 0;
    //@ assert (Double.isNaN(a) && (b == Double.NEGATIVE_INFINITY)) ==> Double.compare(a,b) > 0;
    // @ assert (Double.isNaN(a) && (b == Double.MAX_VALUE)) ==> Double.compare(a,b) > 0;
    //@ assert (Double.isNaN(a) && !Double.isNaN(b)) ==> Double.compare(a,b) > 0;
    //@ assert ((a == Double.POSITIVE_INFINITY) && !Double.isNaN(b)) ==> Double.compare(a,b) >=0;
    //@ assert ((a == Double.POSITIVE_INFINITY) && !Double.isNaN(b) && (b != Double.POSITIVE_INFINITY)) ==> Double.compare(a,b) > 0;
  }
}
