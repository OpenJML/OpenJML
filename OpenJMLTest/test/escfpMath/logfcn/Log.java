public class Log{
  public void logTest1(double a) {
      double b = Math.log(a);
      //@ assert (Double.isNaN(a) || a < 0) <==> Double.isNaN(b);
      //@ assert Double.POSITIVE_INFINITY == a ==> Double.POSITIVE_INFINITY == b;
      //@ assert a == 0 ==> Double.NEGATIVE_INFINITY == b;

      // determine how precise we can actually say this is
      // @ assert Double.isFinite(a) && a > 0 ==> Math.exp(b)-a < .01d;
  }

  //@ requires Double.isFinite(a);
  public static void logTest2(double a)
  {
    double result = Math.log(a);
    //@ assert a == 0.0 ==> result == Double.NEGATIVE_INFINITY;
    //@ assert a > 0.0 ==> Double.isFinite(result);
  }
}
