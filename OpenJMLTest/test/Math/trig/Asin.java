public class Asin{
  //@ requires Double.isFinite(a);
  public static void asinTest(double a)
  {
    double result = Math.asin(a);
    //@ assert ((Double.compare(a, 0.0) != 0) && (Double.compare(a, -0.0) != 0)) && ((Double.compare(a, 1.0) <= 0) && (Double.compare(a, -1.0) >= 0)) ==> !Double.isNaN(result);
    //@ assert (Double.compare(a, 0.0) == 0) ==> (Double.compare(result, 0.0) == 0);
    //@ assert (Double.compare(a, -0.0) == 0) ==> (Double.compare(a, -0.0) == 0);
    //@ assert ((Double.compare(a, 1.0) >= 0) && (Double.compare(a, -1.0) <= 0)) ==> Double.isNaN(result);
  }

  //@ requires !Double.isFinite(a);
  public static void asinTestAnomalies(double a)
  {
    double result = Math.asin(a);
    //@ assert Double.isNaN(result);
  }
}
