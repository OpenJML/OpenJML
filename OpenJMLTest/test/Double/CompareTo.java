/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Double:

.compareTo(double d)


*/


public class CompareTo
{
  public static void compare_literals()
  {
    Double d1 = new Double(0.0);
    Double d2 = new Double(1.0);
    //@ assert d1.compareTo(d1) == 0;
    //@ assert d2.compareTo(d2) == 0;

    //@ assert d1.compareTo(d2) < 0;
    //@ assert d2.compareTo(d1) > 0;

    //@ assert d1.compareTo(new Double(0.0)) == 0;
    //@ assert d2.compareTo(new Double(1.0)) == 0;

    //@ assert d1.compareTo(new Double(1.0)) < 0;
    //@ assert d2.compareTo(new Double(0.0)) > 0;
  }

  //@ requires !Double.isNaN(a) && !Double.isNaN(b);
  public static void compare_finite(double a, double b)
  {
    Double d1 = new Double(a);
    Double d2 = new Double(b);
    //@ assert (a == b) ==> (d1.compareTo(d2) == 0);
    //@ assert (a > b) ==> (d1.compareTo(d2) > 0);
    //@ assert (a < b) ==> (d1.compareTo(d2) < 0);
  }

  public static void compare_nans(double a)
  {
    Double nan = new Double(Double.NaN);
    //@ assert nan.compareTo(new Double(Double.NaN)) == 0;
    //@ assert nan.compareTo(new Double(0.0)) > 0;
    //@ assert nan.compareTo(new Double(Double.POSITIVE_INFINITY)) > 0;
  }

  //@ requires !Double.isNaN(a);
  public static void compare_infinity(double a)
  {
    Double d = new Double(a);
    //@ assert d.compareTo(new Double(Double.POSITIVE_INFINITY)) <= 0;
    //@ assert d.compareTo(new Double(Double.NEGATIVE_INFINITY)) >= 0;
    //@ assert (a == Double.POSITIVE_INFINITY) ==> d.compareTo(new Double(Double.POSITIVE_INFINITY)) == 0;
    //@ assert (a == Double.NEGATIVE_INFINITY) ==> d.compareTo(new Double(Double.NEGATIVE_INFINITY)) == 0;
    //@ assert (a != Double.POSITIVE_INFINITY) ==> d.compareTo(new Double(Double.POSITIVE_INFINITY)) < 0;
    //@ assert (a != Double.NEGATIVE_INFINITY) ==> d.compareTo(new Double(Double.NEGATIVE_INFINITY)) > 0;
  }
}
