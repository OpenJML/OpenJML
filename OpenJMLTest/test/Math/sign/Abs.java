public class Abs
{
  //@ requires Double.isFinite(a);
  public static void absTestFloat(float a)
  {
    float result = Math.abs(a);
    //@ assert Double.isFinite(result);
    //@ assert (Float.compare(result, 0.0f) >= 0);
  }

  //@ requires ! Double.isFinite(a);
  public static void absTestAnomaliesFloat(float a)
  {
    float result = Math.abs(a);
    //@ assert ((Float.compare(a, Float.POSITIVE_INFINITY) == 0) || (Float.compare(a, Float.NEGATIVE_INFINITY) == 0)) ==> (Float.compare(result, Float.POSITIVE_INFINITY) == 0);
    //@ assert Float.isNaN(a) ==> Float.isNaN(result);
  }

  //@ requires Double.isFinite(a);
  public static void absTestDouble(double a)
  {
    double result = Math.abs(a);
    //@ assert Double.isFinite(result);
    //@ assert (Double.compare(result, 0.0) >= 0);
  }

  //@ requires ! Double.isFinite(a);
  public static void absTestAnomaliesDouble(double a)
  {
    double result = Math.abs(a);
    //@ assert ((Double.compare(a, Double.POSITIVE_INFINITY) == 0) || (Double.compare(a, Double.NEGATIVE_INFINITY) == 0)) ==> (Double.compare(result, Double.POSITIVE_INFINITY) == 0);
    //@ assert Double.isNaN(a) ==> Double.isNaN(result);
  }

}
