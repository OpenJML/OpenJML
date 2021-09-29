// written by Robert Moore 5/23/21

public class Cosine {

  // requires (! Double.isNaN(a)) && (! Double.isInfinite(a));
  //@ requires Math.isFinite(a);
  //@ ensures \result >= -1.0 && \result <= 1.0;
  static double inBounds(double a){
    return Math.cos(a);
  }

  //@ ensures \result == 1.0;
  static double cosZero(){
    return Math.cos(0.0);
  }

  //@ requires Double.isFinite(a);
  public static void cosTest(double a)
  {
    double result = Math.cos(a);
    //@ assert Double.isFinite(result) && ((Double.compare(result, 1.0) <= 0) || (Double.compare(result, -1.0) >= 0));
  }

  //@ requires !Double.isFinite(a);
  public static void cosTestAnomalies(double a)
  {
    double result = Math.cos(a);
    // result should be NaN in all cases of non-real input
    //@ assert Double.isNaN(result);
  }
}
