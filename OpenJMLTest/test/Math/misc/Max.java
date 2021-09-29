import java.lang.Math;

public class Max
{

	public static void max_literal_tests()
	{
		double c;
		// integer inputs
		c = Math.max(31, 26);
		//@ assert c == 31.0;
		c = Math.max(-16, -23);
		//@ assert c == -16.0;
		c = Math.max(0, 0);
		//@ assert c == 0.0;

		// floats
		c = Math.max(0.0f, 0.0f);
		//@ assert c == 0.0;
		c = Math.max(-0.0f, -0.0f);
		//@ assert c == 0.0;
		c = Math.max(24.13f, 13.73f);
		//@ assert c == 24.13;
		c = Math.max(-11.56f, -12.10f);
		//@ assert c == -11.56;
		c = Math.max(Float.POSITIVE_INFINITY, Float.POSITIVE_INFINITY);
		//@ assert c == Double.POSITIVE_INFINITY;
		c = Math.max(Float.NEGATIVE_INFINITY, Float.NEGATIVE_INFINITY);
		//@ assert c == Double.NEGATIVE_INFINITY;
		c = Math.max(Float.NaN, Float.NaN);
		//@ assert c != c;

		// doubles
		c = Math.max(0.0, 0.0);
		//@ assert c == 0;
		c = Math.max(-0.0, -0.0);
		//@ assert c == 0;
		c = Math.max(182.28, 582.2004);
		//@ assert c == 582.2004;
		c = Math.max(-19258.4, -404.234);
		//@ assert c == -404.234;
		c = Math.max(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);
		//@ assert c == Double.POSITIVE_INFINITY;
		c = Math.max(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY);
		//@ assert c == Double.NEGATIVE_INFINITY;
		c = Math.max(Double.NaN, Double.NaN);
		//@ assert c != c;
	}



	//@ requires Double.isFinite(a) && Double.isFinite(b);
	public static void max_test_1(double a, double b)
	{
		double c = Math.max(a, b);
		//@ assert a <= b ==> c == b;
		//@ assert b <= a ==> c == a;
	}

	//@ requires Double.isFinite(a) && Double.isFinite(b);
	public static void max_test_2(double a, double b)
	{
	        double c = Math.max(a, b);
		//@ assert c >= a && c >= b;
		//@ assert c == a || c == b;
	}

	//@ requires Double.isFinite(a) && Double.isFinite(b);
	public static void max_test_3(double a, double b)
	{
		double c = Math.max(5 * a - 4, -2 * b + 3);
		//@ assert c >= 5 * a - 4 && c >= -2 * b + 3;
		//@ assert c == 5 * a - 4 || c == -2 * b + 3;
	}


	// if either input is NaN, then output is NaN
	public static void max_NaN_tests(double a, double b)
	{
		double c = Math.max(Double.NaN, Double.NaN);
		//@ assert Double.isNaN(c);

		c = Math.max(Double.NaN, a);
		//@ assert Double.isNaN(c);

		c = Math.max(a, b);
		//@ assert (Double.isNaN(a) || Double.isNaN(b)) ==> Double.isNaN(c);
	}


	public static void max_inf_tests(double a, double b)
	{
		double c = Math.max(Double.POSITIVE_INFINITY, a);
		//@ assert Double.isInfinite(c);

		c = Math.max(Double.NEGATIVE_INFINITY, a);
		//@ assert Double.isFinite(a) ==> Double.isFinite(c);
		//@ assert (a < Double.POSITIVE_INFINITY) ==> Double.isFinite(c);

		c = Math.max(a, b);
		//@ assert (Double.isFinite(a) && Double.isFinite(b)) ==> Double.isFinite(c);

	}



}
