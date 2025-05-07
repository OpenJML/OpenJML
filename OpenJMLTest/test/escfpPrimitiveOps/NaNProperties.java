public /*@ pure @*/ class NaNProperties
{
    // compare zero to NaN values
    public static void zero_comparisons()
    {
      //@ assert !Double.isNaN(0.0);
      //@ assert 0.0 != Double.NaN;
      //@ assert Double.NaN != 0.0;
      //@ assert !(0.0 < Double.NaN);
      //@ assert !(0.0 > Double.NaN);
      //@ assert !(Double.NaN < 0.0);
      //@ assert !(Double.NaN > 0.0);
    }

    public static void literal_comparisons()
    {
      //@ assert !Double.isNaN(32049234.23423);
      //@ assert !Double.isNaN(238432289);
      //@ assert !Double.isNaN(-32049234.23423);
      //@ assert !Double.isNaN(-238432289);
      //@ assert 234.2342E18 != Double.NaN;
      //@ assert Double.NaN != 0.0000001239123;
      //@ assert !(234898223498.23424234 < Double.NaN);
      //@ assert !(-992023490234.23490234 > Double.NaN);
      //@ assert !(Double.NaN < -2234234523.234);
      //@ assert !(Double.NaN > 238429348.8293489234);
    }

    public static void constant_comparisons()
    {
      //@ assert !Double.isNaN(Double.MAX_VALUE);
      //@ assert !Double.isNaN(Double.MIN_VALUE);
      //@ assert !Double.isNaN(-Double.MAX_VALUE);
      //@ assert !Double.isNaN(-Double.MIN_VALUE);
    }

    public static void comparisons(double a)
    {
      //@ assert a != Double.NaN;
      //@ assert Double.NaN != a;
      //@ assert !(a < Double.NaN);
      //@ assert !(a > Double.NaN);
      //@ assert !(Double.NaN < a);
      //@ assert !(Double.NaN > a);
    }

    public static void basicOps(double a, double b){
      //@ assert (!Double.isNaN(a) && !Double.isNaN(b)) ==> !Double.isNaN(a + b);
      //@ assert (Double.isNaN(a) || Double.isNaN(b)) ==> Double.isNaN(a + b);
      //@ assert (!Double.isNaN(a) && !Double.isNaN(b)) ==> !Double.isNaN(a - b);
      //@ assert (Double.isNaN(a) || Double.isNaN(b)) ==> Double.isNaN(a - b);

      //@ assert (Double.isNaN(a) || Double.isNaN(b)) ==> Double.isNaN(a * b);
      //@ assert (Double.isInfinite(a) && (b == 0.0)) ==> Double.isNaN(a * b);
      //@ assert ((a == 0.0) && Double.isInfinite(b)) ==> Double.isNaN(a * b);

      //@ assert (Double.isNaN(a) || Double.isNaN(b)) ==> Double.isNaN(a / b);
      //@ assert (Double.isInfinite(a) && Double.isInfinite(b)) ==> Double.isNaN(a / b);
      //@ assert ((a == 0.0) && (b == 0.0)) ==> Double.isNaN(a / b);
    }
}
