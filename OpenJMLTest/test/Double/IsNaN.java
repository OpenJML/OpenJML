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
    // If we've reached this point, a must be NaN
    //@ assert staticResult == true;
    //@ assert instanceResult == true;
  }
}
