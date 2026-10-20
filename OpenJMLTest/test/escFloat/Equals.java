/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Float:

.equals(Float f)


*/



public class Equals
{
  public static void literal_equals()
  {
    Float a = new Float(0.0);
    //@ assert a.equals(Float.valueOf(0.0f));
    //@ assert ! a.equals(Float.valueOf(1.0f));
    //@ assert (Float.valueOf(0.0f)).equals(Float.valueOf(0.0f));
    //@ assert ! (Float.valueOf(0.0f)).equals(Float.valueOf(1.0f));
  }

  //@ requires !Float.isNaN(d1) && !Float.isNaN(d2);
  public static void arg_equals(float d1, float d2)
  {
    Float a = new Float(d1);
    Float b = new Float(d2);
    //@ assert (d1 == d2 && d1 != 0) ==> a.equals(b);
    //@ assert (d1 == d2 && d1 != 0) ==> b.equals(a);
    //@ assert (d1 != d2) ==> !a.equals(b);
    //@ assert (d1 != d2) ==> !b.equals(a);
  }

  public static void nan_equals()
  {
    Float nan = new Float(Float.NaN);
    //@ assert nan.equals(nan);
    //@ assert nan.equals(Float.valueOf(Float.NaN));
    //@ assert nan.equals(Float.valueOf(nan.floatValue()));
  }

  public static void zero_equals()
  {
    Float pos = new Float(0.0);
    Float neg = new Float(-0.0);
    //@ assert pos.equals(pos);
    //@ assert neg.equals(neg);
    //@ assert !pos.equals(neg);
    //@ assert !neg.equals(pos);
  }
}
