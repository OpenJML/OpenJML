// written by Robert Moore 5/23/21

public class Sine {
  //@ requires Math.isFinite(a);
  //@ ensures \result >= -1.0 && \result <= 1.0;
  static double inBounds(double a){
    return Math.sin(a);
  }

  //@ ensures \result == 0.0;
  static double sinZero(){
    return Math.sin(0.0);
  }

  //@ requires Double.isFinite(a);
  public static void sinTest(double a)
  {
    double result = Math.sin(a);
    //@ assert (Double.compare(a, 0.0) == 0) ==> (Double.compare(result, 0.0) == 0);
    //@ assert (Double.compare(a, -0.0) == 0) ==> (Double.compare(result, -0.0) == 0);
    //@ assert Double.isFinite(result);
  }

  //@ requires !Double.isFinite(a);
  public static void sinTestAnomalies(double a)
  {
    double result = Math.sin(a);
    // result should be NaN in all cases of non-real input
    //@ assert Double.isNaN(result);
  }
}
