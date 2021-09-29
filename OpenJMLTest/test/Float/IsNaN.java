public class IsNaN{
  public static void isNaNTestInstance(float a)
  {
    Float instance = a;
    boolean result = instance.isNaN();
    //@ assert Float.isFinite(a) ==> (result == false);
    //@ assert (Float.floatToIntBits(a) == 0x7fc00000) ==> (result == true);
  }

  public static void isNaNTestStatic(float a)
  {
    boolean result = Float.isNaN(a);
    //@ assert Float.isFinite(a) ==> (result == false);
    //@ assert (Float.floatToIntBits(a) == 0x7fc00000) ==> (result == true);
  }
}
