public class Expm1
{
  //@ requires Double.isFinite(a);
  public static void expm1Test(double a)
  {
    double result = Math.expm1(a);
    //@ assert Double.isFinite(result);
    //@ assert (Double.compare(a, 0.0) == 0) ==> (Double.compare(a, 0.0) == 0);
    //@ assert (Double.compare(a, -0.0) == 0) ==> (Double.compare(a, -0.0) == 0);
  }

  //@ requires ! Double.isFinite(a);
  public static void expm1TestAnomalies(double a)
  {
    double result = Math.expm1(a);
    //@ assert Double.isNaN(a) ==> Double.isNaN(result);
    //@ assert (a == Double.POSITIVE_INFINITY) ==> (result == Double.POSITIVE_INFINITY);
    //@ assert (a == Double.NEGATIVE_INFINITY) ==> (result == -1.0);
  }
}
