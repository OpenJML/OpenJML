public class ToDegrees{
  //@ requires Double.isFinite(a);
  public static void toDegreesTest(double a)
  {
    double result = Math.toDegrees(a);
    //@ assert Double.isFinite(result);
  }
}
