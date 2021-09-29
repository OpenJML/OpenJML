/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Float:

.equals(Float f)


*/



public class Equals
{
  public static void literal_equals()
  {
    Float a = new Float(0.0);
    //@ assert a.equals(new Float(0.0));
    //@ assert ! a.equals(new Float(1.0));
    //@ assert (new Float(0.0)).equals(new Float(0.0));
    //@ assert ! (new Float(0.0)).equals(new Float(1.0));
  }

  //@ requires !Float.isNaN(d1) && !Float.isNaN(d2);
  public static void arg_equals(float d1, float d2)
  {
    Float a = new Float(d1);
    Float b = new Float(d2);
    //@ assert (d1 == d2) ==> a.equals(b);
    //@ assert (d1 == d2) ==> b.equals(a);
    //@ assert (d1 != d2) ==> !a.equals(b);
    //@ assert (d1 != d2) ==> !b.equals(a);
  }

  public static void nan_equals()
  {
    Float nan = new Float(Float.NaN);
    //@ assert nan.equals(nan);
    //@ assert nan.equals(new Float(Float.NaN));
    //@ assert nan.equals(new Float(nan.floatValue()));
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
