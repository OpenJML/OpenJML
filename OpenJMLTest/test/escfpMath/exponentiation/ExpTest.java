public class ExpTest
{
  //@ requires Double.isFinite(a);
  public static void expTest(double a)
  {
    double b = Math.exp(a);
    b = Math.sin(b);
    b = Math.abs(b);
    //@ assert b >= 0.0 && b <= 1.0;
  }
}
