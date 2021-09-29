public class Atan2{
  //@ requires Double.isFinite(a) && Double.isFinite(b);
  public static void atan2Test(double a, double b)
  {
    double result = Math.atan2(a, b);
    //@ assert (Double.compare(a, 0.0) == 0) && (Double.compare(b, 0.0) > 0) ==> (Double.compare(result, 0.0) == 0);
    //@ assert (Double.compare(a, -0.0) == 0) && (Double.compare(b, 0.0) > 0) ==> (Double.compare(result, -0.0) == 0);
    //@ assert (Double.compare(a, 0.0) == 0) && (Double.compare(b, -0.0) < 0) ==> (Double.compare(result, Math.PI) == 0);
    //@ assert (Double.compare(a, -0.0) == 0) && (Double.compare(b, -0.0) < 0) ==> (Double.compare(result, -Math.PI) == 0);
    //@ assert (Double.compare(a, 0.0) > 0) && ((Double.compare(b, 0.0) == 0) || (Double.compare(b, -0.0) == 0)) ==> (Double.compare(result, Math.PI / 2.0) == 0);
    //@ assert (Double.compare(a, -0.0) < 0) && ((Double.compare(b, 0.0) == 0) || (Double.compare(b, -0.0) == 0)) ==> (Double.compare(result, -Math.PI / 2.0) == 0);
  }

  //@ requires !Double.isFinite(a) && Double.isFinite(b);
  public static void atan2TestAAnomalies(double a, double b)
  {
    double result = Math.atan2(a, b);
    //@ assert Double.isNaN(a) ==> Double.isNaN(result);
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, Math.PI / 2.0) == 0);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, -Math.PI / 2.0) == 0);
  }

  //@ requires Double.isFinite(a) && !Double.isFinite(b);
  public static void atan2TestBAnomailes(double a, double b)
  {
    double result = Math.atan2(a, b);
    //@ assert Double.isNaN(b) ==> Double.isNaN(result);
    //@ assert (Double.compare(a, 0.0) > 0) && (Double.compare(b, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, 0.0) == 0);
    //@ assert (Double.compare(a, -0.0) < 0) && (Double.compare(b, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, -0.0) == 0);
    //@ assert (Double.compare(a, 0.0) > 0) && (Double.compare(b, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, Math.PI) == 0);
    //@ assert (Double.compare(a, -0.0) < 0) && (Double.compare(b, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, -Math.PI) == 0);
  }

  //@ requires !Double.isFinite(a) && !Double.isFinite(b);
  public static void atan2TestBothAnomailes(double a, double b)
  {
    double result = Math.atan2(a, b);
    //@ assert (Double.isNaN(a) || Double.isNaN(b)) ==> Double.isNaN(result);
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) && (Double.compare(b, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, Math.PI / 4.0) == 0);
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) && (Double.compare(b, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, 3.0 * (Math.PI / 4.0)) == 0);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) && (Double.compare(b, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, -Math.PI / 4.0) == 0);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) && (Double.compare(b, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, 3.0 * (-Math.PI / 4.0)) == 0);
  }

}
