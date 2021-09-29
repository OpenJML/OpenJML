public class IsInfinite{
  public static void isInfiniteTest(float a)
  {
    boolean result = Float.isInfinite(a);
    //@ assert (Float.compare(a, Float.POSITIVE_INFINITY) == 0) ==> (result == true);
    //@ assert (Float.compare(a, Float.NEGATIVE_INFINITY) == 0) ==> (result == true);
  }

}
