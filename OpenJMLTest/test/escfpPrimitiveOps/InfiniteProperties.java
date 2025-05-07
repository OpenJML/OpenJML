 public /*@ pure @*/ class InfiniteProperties
{
  // verify that positive and negative infinity compare correctly to each other
  public static void signed_infinites()
  {
    //@ assert Double.POSITIVE_INFINITY != Double.NEGATIVE_INFINITY;
    //@ assert Double.POSITIVE_INFINITY > Double.NEGATIVE_INFINITY;
    //@ assert Double.NEGATIVE_INFINITY < Double.POSITIVE_INFINITY;
  }

  // verify that a literal 0.0 compares correctly to both infinities
  public static void compare_zero()
  {
    //@ assert 0.0 != Double.POSITIVE_INFINITY;
    //@ assert 0.0 != Double.NEGATIVE_INFINITY;
    //@ assert 0.0 < Double.POSITIVE_INFINITY;
    //@ assert 0.0 > Double.NEGATIVE_INFINITY;
  }
  
  public static void inequality_literals()
  {
  //@ assert 0 != Double.POSITIVE_INFINITY;
  //@ assert 29348394.23494 != Double.POSITIVE_INFINITY;
  //@ assert -23489348.23482934829348 != Double.NEGATIVE_INFINITY;
  //@ assert 234243E20 != Double.POSITIVE_INFINITY;
  }
  
  public static void comparison_literals()
  {
  //@ assert 0 < Double.POSITIVE_INFINITY;
  //@ assert 29348394.23494 < Double.POSITIVE_INFINITY;
  //@ assert -23489348.23482934829348 > Double.NEGATIVE_INFINITY;
  //@ assert -234243E20 > Double.NEGATIVE_INFINITY;
  }
  
  public static void inequality_constants()
  {
  //@ assert Double.MAX_VALUE != Double.POSITIVE_INFINITY;
  //@ assert Double.MAX_VALUE != Double.NEGATIVE_INFINITY;
  //@ assert -Double.MAX_VALUE != Double.POSITIVE_INFINITY;
  //@ assert -Double.MAX_VALUE != Double.NEGATIVE_INFINITY;
  }
  
  public static void comparison_constants()
  {
  //@ assert Double.MAX_VALUE < Double.POSITIVE_INFINITY;
  //@ assert Double.MAX_VALUE > Double.NEGATIVE_INFINITY;
  //@ assert -Double.MAX_VALUE < Double.POSITIVE_INFINITY;
  //@ assert -Double.MAX_VALUE > Double.NEGATIVE_INFINITY;
  }

  public static void sign_tests()
  {
  //@ assert Double.POSITIVE_INFINITY == -Double.NEGATIVE_INFINITY;
  //@ assert Double.NEGATIVE_INFINITY == -Double.POSITIVE_INFINITY;
  }

  // verify that signed infinity results from division by zero with double literals
  public static void division_by_zero()
  {
    //@ ghost double a = 1.0 / 0.0;
    //@ assert a == Double.POSITIVE_INFINITY;
    //@ ghost double b = -1.0 / 0.0;
    //@ assert b == Double.NEGATIVE_INFINITY;
  }

  // verify that an non-NaN double variable compares correctly to both infinities
  //@ requires !Double.isNaN(a);
  public static void comparisons(double a)
  {
    //@ assert a <= Double.POSITIVE_INFINITY;
    //@ assert a >= Double.NEGATIVE_INFINITY;
    //@ assert ((a != Double.POSITIVE_INFINITY)) ==> (a < Double.POSITIVE_INFINITY);
    //@ assert ((a != Double.NEGATIVE_INFINITY)) ==> (a > Double.NEGATIVE_INFINITY);

  }

  //@ requires !Double.isNaN(a) && !Double.isNaN(b);
  public static void addition(double a, double b)
  {
    //@ assert (a == Double.POSITIVE_INFINITY && b != Double.NEGATIVE_INFINITY) ==> (a + b) == Double.POSITIVE_INFINITY;
    //@ assert (a != Double.POSITIVE_INFINITY && b == Double.NEGATIVE_INFINITY) ==> (a + b) == Double.NEGATIVE_INFINITY;
    //@ assert (a == Double.POSITIVE_INFINITY && b == Double.NEGATIVE_INFINITY) ==> Double.isNaN(a + b);
  }

  //@ requires !Double.isNaN(a) && !Double.isNaN(b);
  public static void subtraction(double a, double b)
  {
    //@ assert (a == Double.POSITIVE_INFINITY && b != Double.POSITIVE_INFINITY) ==> (a - b) == Double.POSITIVE_INFINITY;
    //@ assert (a != Double.POSITIVE_INFINITY && b == Double.POSITIVE_INFINITY) ==> (a - b) == Double.NEGATIVE_INFINITY;
    //@ assert (a == Double.POSITIVE_INFINITY && b == Double.POSITIVE_INFINITY) ==> Double.isNaN(a - b);
  }

  //@ requires !Double.isNaN(a) && !Double.isNaN(b);
  public static void multiplication(double a, double b)
  {
    //@ assert (a == Double.POSITIVE_INFINITY && b == 0.0) ==> Double.isNaN(a * b);
    //@ assert (a == Double.POSITIVE_INFINITY && b > 0.0) ==> (a * b) == Double.POSITIVE_INFINITY;
    //@ assert (a == Double.POSITIVE_INFINITY && b < 0.0) ==> (a * b) == Double.NEGATIVE_INFINITY;
    //@ assert (a == Double.NEGATIVE_INFINITY && b == 0.0) ==> Double.isNaN(a * b);
    //@ assert (a == Double.NEGATIVE_INFINITY && b > 0.0) ==> (a * b) == Double.NEGATIVE_INFINITY;
    //@ assert (a == Double.NEGATIVE_INFINITY && b < 0.0) ==> (a * b) == Double.POSITIVE_INFINITY;
  }

  //@ requires !Double.isNaN(a) && !Double.isNaN(b);
  public static void division(double a, double b)
  {
    //@ assert ((a == Double.POSITIVE_INFINITY || a == Double.NEGATIVE_INFINITY) && (b == Double.POSITIVE_INFINITY || b == Double.NEGATIVE_INFINITY)) ==> Double.isNaN(a / b);
    //@ assert (a == Double.POSITIVE_INFINITY && (b > 0.0 && b < Double.POSITIVE_INFINITY)) ==> (a / b) == Double.POSITIVE_INFINITY;
    //@ assert (a == Double.POSITIVE_INFINITY && (b > Double.NEGATIVE_INFINITY && b < 0.0)) ==> (a / b) == Double.NEGATIVE_INFINITY;
    //@ assert ((a > Double.NEGATIVE_INFINITY && a < Double.POSITIVE_INFINITY) && (b == Double.POSITIVE_INFINITY || b == Double.NEGATIVE_INFINITY)) ==> (a / b) == 0.0;
    //@ assert (a != 0.0 && b == 0.0) ==> (a / b) == Double.POSITIVE_INFINITY || (a / b) == Double.NEGATIVE_INFINITY;
  }
}
