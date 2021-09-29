public class Max{
  //@ requires Double.isFinite(a) && Double.isFinite(b);
  public static void maxTest(double a, double b)
  {
    double result = Double.max(a, b);
    //@ assert (a > b) ==> result == a;
    //@ assert (a < b) ==> result == b;
  }

  //@ requires !Double.isFinite(a) && Double.isFinite(b);
  public static void maxTestAAnomalies(double a, double b)
  {
    double result = Double.max(a, b);
    //@ assert (Double.isNaN(a)) ==> (Double.compare(result, b) == 0);
    //@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, a) == 0);
    //@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, b) == 0);
  }

  //@ requires Double.isFinite(a) && !Double.isFinite(b);
  public static void maxTestBAnomalies(double a, double b)
  {
    double result = Double.max(a, b);
    //@ assert (Double.isNaN(b)) ==> (Double.compare(result, a) == 0);
    //@ assert (Double.compare(b, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, b) == 0);
    //@ assert (Double.compare(b, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, a) == 0);
  }

  //@ requires !Double.isFinite(a) && !Double.isFinite(b);
  public static void maxTestBothAnomalies(double a, double b)
  {
    double result = Double.max(a, b);
    //@ assert (Double.isNaN(a) && Double.isNaN(b)) ==> (Double.isNaN(result));
    //@ assert (Double.isNaN(a) && !Double.isNaN(b)) ==> (Double.compare(b, result) == 0);
    //@ assert (!Double.isNaN(a) && Double.isNaN(b)) ==> (Double.compare(a, result) == 0);
    //@ assert ((Double.compare(a, Double.POSITIVE_INFINITY) == 0) && (Double.compare(b, Double.POSITIVE_INFINITY) == 0)) ==> (Double.compare(result, Double.POSITIVE_INFINITY) == 0);
    //@ assert ((Double.compare(a, Double.POSITIVE_INFINITY) == 0) && (Double.compare(b, Double.NEGATIVE_INFINITY) == 0)) ==> (Double.compare(result, Double.POSITIVE_INFINITY) == 0);
    //@ assert ((Double.compare(a, Double.NEGATIVE_INFINITY) == 0) && (Double.compare(b, Double.NEGATIVE_INFINITY) == 0)) ==> (Double.compare(result, Double.NEGATIVE_INFINITY) == 0);
    //@ assert ((Double.compare(a, Double.NEGATIVE_INFINITY) == 0) && (Double.compare(b, Double.POSITIVE_INFINITY) == 0)) ==> (Double.compare(result, Double.POSITIVE_INFINITY) == 0);
  }
}
