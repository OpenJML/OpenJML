// written by Robert Moore 5/26/21

public class Trig {
  //@ requires Math.isFinite(d);
  //@ ensures (\result < 1.001) && (\result > 0.999);
  static double squareSum(double d){
    double a = Math.sin(d) * Math.sin(d);
    double b = Math.cos(d) * Math.cos(d);
    return a + b;
  }
}
