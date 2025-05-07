public class Tan{
  //@ requires Double.isFinite(a);
  public static void tanTest(double a)
  {
    double result = Math.tan(a);
    //@ assert (Double.compare(a, 0.0) == 0) ==> (Double.compare(result, 0.0) == 0);
    //@ assert (Double.compare(a, -0.0) == 0) ==> (Double.compare(result, -0.0) == 0);
  }

  //@ requires !Double.isFinite(a);
  public static void tanTestAnomalies(double a)
  {
    double result = Math.tan(a);
    // result should be NaN in all cases of non-real input
    //@ assert Double.isNaN(result);
  }

}
