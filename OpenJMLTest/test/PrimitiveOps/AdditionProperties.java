 public class AdditionProperties {
  //@ requires Double.isFinite(a) && Double.isFinite(b) && Double.isFinite(a+b);
  public static void finiteAddition(double a, double b){
    double c = a + b;
    //@ assert Double.isFinite(c);
    //@ assert (a > 0.0) && (b > 0.0) ==> (c > 0.0);
    //@ assert (a < 0.0) && (b < 0.0) ==> (c < 0.0);
    //@ assert (a > 0.0) && (b < 0.0) && (Math.abs(a) > Math.abs(b)) ==> (c > 0.0);
    //@ assert (a > 0.0) && (b < 0.0) && (Math.abs(a) < Math.abs(b)) ==> (c < 0.0);
  }
}
