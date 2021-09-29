public class Atan{
  //@ requires Double.isFinite(a);
  public static void atanTest(double a)
  {
    double result = Math.atan(a);
    //@ assert (Double.compare(a, 0.0) == 0) ==> (Double.compare(a, 0.0) == 0);
    //@ assert (Double.compare(a, -0.0) == 0) ==> (Double.compare(a, -0.0) == 0);
    //@ assert Double.isFinite(result);
  }

  //@ requires !Double.isFinite(a);
  public static void atanTestAnomalies(double a)
  {
    double result = Math.atan(a);
    //@ assert Double.isNaN(a) ==> Double.isNaN(result);
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, Double.POSITIVE_INFINITY) == 0);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, Double.NEGATIVE_INFINITY) == 0);
  }
}
