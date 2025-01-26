public class GetExponent
{
  //@ requires Double.isFinite(a);
  public static void getExponentTest(double a)
  {
    double result = Math.getExponent(a);
    //@ assert Double.isFinite(result);
    //@ assert (a == 0.0) ==> (result == Double.MIN_EXPONENT - 1.0);
  }

  //@ requires ! Double.isFinite(a);
  public static void getExponentTestAnomalies(double a)
  {
    double result = Math.getExponent(a);
    //@ assert Double.isNaN(a) ==> (Double.compare(result, Double.MAX_EXPONENT - 1.0) == 0);
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, Double.MAX_EXPONENT + 1) == 0);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, Double.MAX_EXPONENT + 1) == 0);
  }

}
