
/*
THIS PROGRAM TESTS THE FOLLOWING CONSTRUCTORS FROM java.lang.Float:

Float(float f)
Float(String s)


*/

public class Constructors
{
  public static void float_constructor(float f)
  {
    Float wrapper = new Float(f);
    //@ assert wrapper.equals(Float.valueOf(f));
    //@ assert wrapper.equals(Float.valueOf(wrapper.floatValue()));
    //@ assert !Float.isNaN(f) ==> f == wrapper.floatValue();
    //@ assert Float.isNaN(f) ==> Float.isNaN(wrapper.floatValue());
    //@ assert Float.isNaN(f) ==> wrapper.isNaN();
  }

  public static void double_constructor(double d)
  {
    Float wrapper = new Float(d);
    //@ assert wrapper.equals(Float.valueOf((float)d));
    //@ assert (d == Double.POSITIVE_INFINITY) ==> wrapper.floatValue() == Float.POSITIVE_INFINITY;
    //@ assert (d == Double.NEGATIVE_INFINITY) ==> wrapper.floatValue() == Float.NEGATIVE_INFINITY;
    //@ assert Double.isNaN(d) ==> Float.isNaN(wrapper.floatValue());
    //@ assert Double.isNaN(d) ==> wrapper.isNaN();
  }

  public static void string_constructor(String s)
  {
    Float wrapper = new Float(s);
    //@ assert s.equals("NaN") ==> Float.isNaN(wrapper.floatValue());
    //@ assert s.equals("Infinity") ==> wrapper.floatValue() == Float.POSITIVE_INFINITY;
    //@ assert s.equals("-Infinity") ==> wrapper.floatValue() == Float.NEGATIVE_INFINITY;
    //@ assert wrapper.equals(Float.valueOf(wrapper.toString()));
  }
}
