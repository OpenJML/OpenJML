public class IsInfinite {
  //@ requires Double.isFinite(a);
  public static void isInfiniteTest(double a)
  {
    boolean staticResult = Double.isInfinite(a);
    Double instance = a;
    boolean instanceResult = instance.isInfinite();
    //@ assert staticResult == false;
    //@ assert instanceResult == false;
  }

  //@ requires !Double.isFinite(a);
  public static void isInfiniteTestAnomalies(double a)
  {
    boolean staticResult = Double.isFinite(a);
    Double instance = a;
    boolean instanceResult = instance.isInfinite();
    //@ assert Double.isNaN(a) ==> (staticResult == false);
    //@ assert !Double.isNaN(a) ==> (staticResult == true);
    //@ assert instance.isNaN() ==> (instanceResult == false);
    //@ assert !instance.isNaN() ==> (instanceResult == true);
  }
}
