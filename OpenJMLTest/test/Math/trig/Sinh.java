public class Sinh{
  //@ requires Double.isFinite(a);
  public static void sinhTest(double a)
  {
    double result = Math.sinh(a);
    //@ assert Double.isFinite(result);
    //@ assert (Double.compare(a, 0.0) == 0) ==> (Double.compare(result, 0.0) == 0);
    //@ assert (Double.compare(a, -0.0) == 0) ==> (Double.compare(result, -0.0) == 0);
  }

  //@ requires !Double.isFinite(a);
  public static void sinhTestAnomalies(double a)
  {
    double result = Math.sinh(a);
    //@ assert Double.isNaN(a) ==> Double.isNaN(result);
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, Double.POSITIVE_INFINITY) == 0);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, Double.NEGATIVE_INFINITY) == 0);
  }
}
