import java.lang.Math;

public class Hypot
{
	//@ requires a == 0.0;
	public static void hypot_test_1(double a, double b)
	{
		double c = Math.hypot(a, b);
		//@ assert Math.close(b,c,3.0E-16);
	}

	//@ requires a == 0.0 && b == 0.0;
	public static void hypot_test_2(double a, double b)
	{
	        double c = Math.hypot(a, b);
		//@ assert c == 0.0;
	}

	//@ requires a == 1.0 && b == 0.0;
	public static void hypot_test_3(double a, double b)
	{
	        double c = Math.hypot(a, b);
	        //@ assert c == 1.0;
	}


	// If either argument is infinite, the result is positive infinity
	public static void hypot_inf_test(double a, double b)
	{
		double c = Math.hypot(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);
		//@ assert Double.isInfinite(c);

		c = Math.hypot(a, Double.POSITIVE_INFINITY);
		//@ assert Double.isInfinite(c);

		c = Math.hypot(Double.POSITIVE_INFINITY, b);
		//@ assert Double.isInfinite(c);

		c = Math.hypot(a, Double.NEGATIVE_INFINITY);
		//@ assert Double.isInfinite(c);

		c = Math.hypot(Double.NEGATIVE_INFINITY, b);
		//@ assert Double.isInfinite(c);

		c = Math.hypot(a, b);
		//@ assert (Double.isInfinite(a) || Double.isInfinite(b)) ==> Double.isInfinite(c);
	}

	// If either argument is NaN and no arguments are infinite, the result is NaN
	public static void hypot_nan_test(double a, double b)
	{
		double c = Math.hypot(Double.NaN, Double.NaN);
		//@ assert Double.isNaN(c);

		c = Math.hypot(a, Double.NaN);
		//@ assert !Double.isInfinite(a) ==> Double.isNaN(c);

		c = Math.hypot(Double.NaN, b);
		//@ assert !Double.isInfinite(b) ==> Double.isNaN(c);

		c = Math.hypot(a, b);
		//@ assert ( (Double.isNaN(a) || Double.isNaN(b)) &&  !Double.isInfinite(a) && !Double.isInfinite(b) )  ==> Double.isNaN(c);
	}
}
