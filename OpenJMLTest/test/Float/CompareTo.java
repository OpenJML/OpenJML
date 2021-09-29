/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Float:

.compareTo(Float f2)


*/


public class CompareTo
{
  public static void compare_literals()
  {
    Float f1 = new Float(0.0f);
    Float f2 = new Float(1.0f);
    //@ assert f1.compareTo(f1) == 0;
    //@ assert f2.compareTo(f2) == 0;

    //@ assert f1.compareTo(f2) < 0;
    //@ assert f2.compareTo(f1) > 0;

    //@ assert f1.compareTo(new Float(0.0f)) == 0;
    //@ assert f2.compareTo(new Float(1.0f)) == 0;

    //@ assert f1.compareTo(new Float(1.0f)) < 0;
    //@ assert f2.compareTo(new Float(0.0f)) > 0;
  }

  //@ requires !Float.isNaN(a) && !Float.isNaN(b);
  public static void compare_finite(float a, float b)
  {
    Float f1 = new Float(a);
    Float f2 = new Float(b);
    //@ assert (a == b) ==> (f1.compareTo(f2) == 0);
    //@ assert (a > b) ==> (f1.compareTo(f2) > 0);
    //@ assert (a < b) ==> (f1.compareTo(f2) < 0);
  }

  public static void compare_nans(float a)
  {
    Float nan = new Float(Float.NaN);
    //@ assert nan.compareTo(new Float(Float.NaN)) == 0;
    //@ assert nan.compareTo(new Float(0.0f)) > 0;
    //@ assert nan.compareTo(new Float(Float.POSITIVE_INFINITY)) > 0;
  }

  //@ requires !Float.isNaN(a);
  public static void compare_infinity(float a)
  {
    Float f = new Float(a);
    //@ assert f.compareTo(new Float(Float.POSITIVE_INFINITY)) <= 0;
    //@ assert f.compareTo(new Float(Float.NEGATIVE_INFINITY)) >= 0;
    //@ assert (a == Float.POSITIVE_INFINITY) ==> f.compareTo(new Float(Float.POSITIVE_INFINITY)) == 0;
    //@ assert (a == Float.NEGATIVE_INFINITY) ==> f.compareTo(new Float(Float.NEGATIVE_INFINITY)) == 0;
    //@ assert (a != Float.POSITIVE_INFINITY) ==> f.compareTo(new Float(Float.POSITIVE_INFINITY)) < 0;
    //@ assert (a != Float.NEGATIVE_INFINITY) ==> f.compareTo(new Float(Float.NEGATIVE_INFINITY)) > 0;
  }
}
