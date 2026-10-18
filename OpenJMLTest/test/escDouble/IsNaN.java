public class IsNaN{
  //@ requires Double.isFinite(a);
  public static void isNaNTest(double a)
  {
    boolean staticResult = Double.isNaN(a);
    Double instance = a;
    boolean instanceResult = instance.isNaN();
    //@ assert staticResult == false;
    //@ assert instanceResult == false;
  }

  //@ requires !Double.isFinite(a);
  public static void isNaNTestAnomalies(double a)
  {
    boolean staticResult = Double.isNaN(a);
    Double instance = a;
    boolean instanceResult = instance.isNaN();
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (staticResult == false);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (staticResult == false);
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (instanceResult == false);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (instanceResult == false);
    //@ assert !Double.isInfinite(a) ==> staticResult;
    //@ assert !Double.isInfinite(a) ==> instanceResult;
  }
}
