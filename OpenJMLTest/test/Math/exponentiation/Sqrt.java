public class Sqrt
{
  //@ requires Double.isFinite(a);
  public static void sqrtTest(double a)
  {
    double result = Math.sqrt(a);
    //@ assert (a >= 0.0) ==> (Double.isFinite(result) && result >= 0.0);
    //@ assert (a < 0.0) ==> Double.isNaN(result);
  }

  public static void sqrtTestAnomalies(double a)
  {
    double result = Math.sqrt(a);
    //@ assert Double.isNaN(a) ==> Double.isNaN(result);
    //@ assert (a == Double.POSITIVE_INFINITY) ==> (result == Double.POSITIVE_INFINITY);
  }
}
