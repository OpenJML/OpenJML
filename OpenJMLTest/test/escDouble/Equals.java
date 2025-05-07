/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Double:
.equals(Double d)

*/



public class Equals
{
  public static void literal_equals()
  {
    Double a = new Double(0.0);
    //@ assert a.equals(Double.valueOf(0.0));
    //@ assert ! a.equals(Double.valueOf(1.0));
    //@ assert (Double.valueOf(0.0)).equals(Double.valueOf(0.0));
    //@ assert ! (Double.valueOf(0.0)).equals(Double.valueOf(1.0));
  }

  //@ requires !Double.isNaN(d1) && !Double.isNaN(d2);
  public static void arg_equals(double d1, double d2)
  {
    Double a = new Double(d1);
    Double b = new Double(d2);
    //@ assert (d1 == d2) ==> a.equals(b);
    //@ assert (d1 == d2) ==> b.equals(a);
    //@ assert (d1 != d2) ==> !a.equals(b);
    //@ assert (d1 != d2) ==> !b.equals(a);
  }

  public static void nan_equals()
  {
    Double nan = new Double(Double.NaN);
    //@ assert nan.equals(nan);
    //@ assert nan.equals(Double.valueOf(Double.NaN));
    //@ assert nan.equals(Double.valueOf(nan.doubleValue()));
  }

  public static void zero_equals()
  {
    Double pos = new Double(0.0);
    Double neg = new Double(-0.0);
    //@ assert pos.equals(pos);
    //@ assert neg.equals(neg);
    //@ assert !pos.equals(neg);
    //@ assert !neg.equals(pos);
  }
}
