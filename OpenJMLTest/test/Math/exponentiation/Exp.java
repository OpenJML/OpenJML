public class Exp
{
  //@ requires Double.isFinite(a);
  public static void expTest(double a)
  {
    double result = Math.exp(a);
    //@ assert Double.isFinite(result);
  }

  //@ requires ! Double.isFinite(a);
  public static void expTestAnomalies(double a)
  {
    double result = Math.exp(a);
    //@ assert Double.isNaN(a) ==> Double.isNaN(result);
    //@ assert (a == Double.POSITIVE_INFINITY) ==> (result == Double.POSITIVE_INFINITY);
    //@ assert (a == Double.NEGATIVE_INFINITY) ==> Math.isPositiveZero(result);
  }
}
