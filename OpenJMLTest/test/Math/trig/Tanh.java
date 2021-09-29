public class Tanh{
  //@ requires Double.isFinite(a);
  public static void tanhTest(double a)
  {
    double result = Math.tanh(a);
    //@ assert (Double.compare(a, 0.0) == 0) ==> (Double.compare(result, 0.0) == 0);
    //@ assert (Double.compare(a, -0.0) == 0) ==> (Double.compare(result, -0.0) == 0);
  }

  //@ requires !Double.isFinite(a);
  public static void tanhTestAnomalies(double a)
  {
    double result = Math.tanh(a);
    //@ assert Double.isNaN(a) ==> Double.isNaN(result);
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, 1.0) == 0);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, -1.0) == 0);
  }
}
