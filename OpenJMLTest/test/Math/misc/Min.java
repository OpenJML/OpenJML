import java.lang.Math;

public class Min
{




	public static void min_literal_tests()
	{
		double c;
		// integer inputs
		c = Math.min(31, 26);
		//@ assert c == 26.0;
		c = Math.min(-16, -23);
		//@ assert c == -23.0;
		c = Math.min(0, 0);
		//@ assert c == 0.0;

		// floats
		c = Math.min(0.0f, 0.0f);
		//@ assert c == 0.0;
		c = Math.min(-0.0f, -0.0f);
		//@ assert c == 0.0;
		c = Math.min(Float.POSITIVE_INFINITY, Float.POSITIVE_INFINITY);
		//@ assert c == Double.POSITIVE_INFINITY;
		c = Math.min(Float.NEGATIVE_INFINITY, Float.NEGATIVE_INFINITY);
		//@ assert c == Double.NEGATIVE_INFINITY;
		c = Math.min(Float.NaN, Float.NaN);
		//@ assert c != c;

		// doubles
		c = Math.min(0.0, 0.0);
		//@ assert c == 0;
		c = Math.min(-0.0, -0.0);
		//@ assert c == 0;
		c = Math.min(182.28, 582.2004);
		//@ assert c == 182.28;
		c = Math.min(-19258.4, -404.234);
		//@ assert c == -19258.4;
		c = Math.min(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);
		//@ assert c == Double.POSITIVE_INFINITY;
		c = Math.min(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY);
		//@ assert c == Double.NEGATIVE_INFINITY;
		c = Math.min(Double.NaN, Double.NaN);
		//@ assert c != c;
	}


	//@ requires Double.isFinite(a) && Double.isFinite(b);
	public static void min_test_1(double a, double b)
	{
		double c = Math.min(a, b);
		//@ assert a <= b ==> c == a;
		//@ assert b <= a ==> c == b;
	}


	//@ requires Double.isFinite(a) && Double.isFinite(b);
	public static void min_test_2(double a, double b)
	{
	        double c = Math.min(a, b);
		//@ assert c <= a && c <= b;
		//@ assert c == a || c == b;
	}


	//@ requires Double.isFinite(a) && Double.isFinite(b);
	public static void min_test_3(double a, double b)
	{
		double c = Math.min(5 * a - 4, -2 * b + 3);
		//@ assert c <= 5*a - 4 && c <= -2*b + 3;
		//@ assert c == 5*a - 4 || c == -2*b + 3;
	}


	public static void min_NaN_tests(double a, double b)
	{
		double c = Math.min(Double.NaN, Double.NaN);
		//@ assert Double.isNaN(c);

		c = Math.min(Double.NaN, a);
		//@ assert Double.isNaN(c);

		c = Math.min(a, b);
		//@ assert (Double.isNaN(a) || Double.isNaN(b)) ==> Double.isNaN(c);
		//@ assert (!Double.isNaN(a) && !Double.isNaN(b)) ==> !Double.isNaN(c);
	}

	public static void min_inf_tests(double a, double b)
	{
		double c = Math.min(Double.NEGATIVE_INFINITY, a);
		//@ assert Double.isInfinite(c);

		c = Math.min(Double.POSITIVE_INFINITY, a);
		//@ assert Double.isFinite(a) ==> Double.isFinite(c);
		//@ assert (a > Double.NEGATIVE_INFINITY) && (a != Double.POSITIVE_INFINITY) ==> Double.isFinite(c);

		c = Math.min(a, b);
		//@ assert (Double.isFinite(a) && Double.isFinite(b)) ==> Double.isFinite(c);
		//@ assert (Double.isInfinite(a) && Double.isInfinite(b)) ==> Double.isInfinite(c);
		//@ assert Double.isInfinite(c) ==> (Double.isInfinite(a) || Double.isInfinite(b));
	}

}
