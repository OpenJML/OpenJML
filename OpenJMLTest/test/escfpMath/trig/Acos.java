public class Acos{
  //@ requires Double.isFinite(a);
  public static void acosTest(double a)
  {
    double result = Math.acos(a);
    //@ assert ((Double.compare(a, 1.0) <= 0) && (Double.compare(a, -1.0) >= 0)) ==> !Double.isNaN(result);
    //@ assert ((Double.compare(a, 1.0) >= 0) && (Double.compare(a, -1.0) <= 0)) ==> Double.isNaN(result);
  }

  //@ requires !Double.isFinite(a);
  public static void acosTestAnomalies(double a)
  {
    double result = Math.acos(a);
    //@ assert Double.isNaN(result);
  }
}
