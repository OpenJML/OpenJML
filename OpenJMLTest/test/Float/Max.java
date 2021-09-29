public class Max{
  //@ requires Double.isFinite(a) && Double.isFinite(b);
  public static void maxTest(float a, float b)
  {
    float result = Float.max(a, b);
    //@ assert (Float.compare(a, b) >= 0) ==> (Float.compare(result, a) == 0);
    //@ assert (Float.compare(a, b) < 0) ==> (Float.compare(result, b) == 0);
  }

  //@ requires !Double.isFinite(a) && Double.isFinite(b);
  public static void maxTestAAnomalies(float a, float b)
  {
    float result = Float.max(a, b);
    //@ assert (Float.isNaN(a)) ==> (Float.compare(result, b) == 0);
    //@ assert (Float.compare(a, Float.POSITIVE_INFINITY) == 0) ==> (Float.compare(result, a) == 0);
    //@ assert (Float.compare(a, Float.NEGATIVE_INFINITY) == 0) ==> (Float.compare(result, b) == 0);
  }

  //@ requires Double.isFinite(a) && !Double.isFinite(b);
  public static void maxTestBAnomalies(float a, float b)
  {
    float result = Float.max(a, b);
    //@ assert (Float.isNaN(b)) ==> (Float.compare(result, a) == 0);
    //@ assert (Float.compare(b, Float.POSITIVE_INFINITY) == 0) ==> (Float.compare(result, b) == 0);
    //@ assert (Float.compare(b, Float.NEGATIVE_INFINITY) == 0) ==> (Float.compare(result, a) == 0);
  }

  //@ requires !Double.isFinite(a) && !Double.isFinite(b);
  public static void maxTestBothAnomalies(float a, float b)
  {
    float result = Float.max(a, b);
    //@ assert (Float.isNaN(a) && Float.isNaN(b)) ==> (Float.isNaN(result));
    //@ assert (Float.isNaN(a) && !Float.isNaN(b)) ==> (Float.compare(b, result) == 0);
    //@ assert (!Float.isNaN(a) && Float.isNaN(b)) ==> (Float.compare(a, result) == 0);
    //@ assert ((Float.compare(a, Float.POSITIVE_INFINITY) == 0) && (Float.compare(b, Float.POSITIVE_INFINITY) == 0)) ==> (Float.compare(result, Float.POSITIVE_INFINITY) == 0);
    //@ assert ((Float.compare(a, Float.POSITIVE_INFINITY) == 0) && (Float.compare(b, Float.NEGATIVE_INFINITY) == 0)) ==> (Float.compare(result, Float.POSITIVE_INFINITY) == 0);
    //@ assert ((Float.compare(a, Float.NEGATIVE_INFINITY) == 0) && (Float.compare(b, Float.NEGATIVE_INFINITY) == 0)) ==> (Float.compare(result, Float.NEGATIVE_INFINITY) == 0);
    //@ assert ((Float.compare(a, Float.NEGATIVE_INFINITY) == 0) && (Float.compare(b, Float.POSITIVE_INFINITY) == 0)) ==> (Float.compare(result, Float.POSITIVE_INFINITY) == 0);
  }
}
