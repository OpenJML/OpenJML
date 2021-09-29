/*
THIS PROGRAM TESTS THE FOLLOWING CONSTRUCTORS FROM java.lang.Double:

Double(double d)
Double(String s)


*/


public class Constructors
{
  public static void double_constructor(double d)
  {
    Double wrapper = new Double(d);
    //@ assert wrapper.equals(new Double(d));
    //@ assert wrapper.equals(new Double(wrapper.doubleValue()));
    //@ assert !Double.isNaN(d) ==> d == wrapper.doubleValue();
    //@ assert Double.isNaN(d) ==> Double.isNaN(wrapper.doubleValue());
    //@ assert Double.isNaN(d) ==> wrapper.isNaN();
  }

  public static void string_constructor(String s)
  {
    Double wrapper = new Double(s);
    //@ assert s.equals("NaN") ==> Double.isNaN(wrapper.doubleValue());
    //@ assert s.equals("Infinity") ==> wrapper.doubleValue() == Double.POSITIVE_INFINITY;
    //@ assert s.equals("-Infinity") ==> wrapper.doubleValue() == Double.NEGATIVE_INFINITY;
    //@ assert wrapper.equals(new Double(wrapper.toString()));
  }
}
