public class Cosh{
  //@ requires Double.isFinite(a);
  public static void coshTest(double a)
  {
    double result = Math.cosh(a);
    //@ assert (Double.compare(a, 0.0) == 0) ==> (Double.compare(result, 1.0) == 0);
    //@ assert Double.isFinite(result);
  }

  //@ requires !Double.isFinite(a);
  public static void coshTestAnomalies(double a)
  {
    double result = Math.cosh(a);
    //@ assert Double.isNaN(a) ==> Double.isNaN(result);
    //@ assert !Double.isFinite(a) ==> (Double.compare(result, Double.POSITIVE_INFINITY) == 0);
  }
}
