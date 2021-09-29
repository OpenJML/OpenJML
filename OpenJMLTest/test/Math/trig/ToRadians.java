public class ToRadians{
  //@ requires Double.isFinite(a);
  public static void toRadiansTest(double a)
  {
    double result = Math.toRadians(a);
    //@ assert Double.isFinite(result);
  }
}
