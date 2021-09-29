/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Double:

Double.sum(double d1, double d2)

Double.min(double d1, double d2)


*/

public class OpsTests
{


public static void sum_literal_tests()
{
	double a, b, c;
	
	//integers
	a = 1;
	b = 1;
	c = Double.sum(a, b);
	//@ assert c == (double) 2;
	a = -2;
	b = 2;
	c = Double.sum(a, b);
	//@ assert c == (double) 0;
	a = 142;
	b = 18;
	c = Double.sum(a, b);
	//@ assert c == (double) 160;
	
	//floats
	a = 181.345f;
	b = 842.22f;
	c = Double.sum(a, b);
	//@ assert c == (double) ( a + b);
	a = -291.585f;
	b = -294949.33f;
	c = Double.sum(a, b);
	//@ assert c == (double) (a+b);
	a = Float.NaN;
	b = 185.5f;
	c = Double.sum(a, b);
	//@ assert Double.isNaN(c);
	a = Float.POSITIVE_INFINITY;
	b = Float.POSITIVE_INFINITY;
	c = Double.sum(a, b);
	//@ assert c == Double.POSITIVE_INFINITY;
	a = Float.NEGATIVE_INFINITY;
	b = Float.NEGATIVE_INFINITY;
	c = Double.sum(a, b);
	//@ assert c == Double.NEGATIVE_INFINITY;
	a = Float.NEGATIVE_INFINITY;
	b = Float.POSITIVE_INFINITY;
	c = Double.sum(a, b);
	//@ assert Double.isNaN(c);
	
	//doubles
	a = 15058.543;
	b = -15058.543;
	c = Double.sum(a, b);
	//@ assert c == 0;
	a = 583.255;
	b = 384834.33;
	c = Double.sum(a, b);
	//@ assert c == a + b;
	a = -291.585;
	b = -294949.33;
	c = Double.sum(a, b);
	//@ assert c == (double) (a+b);
	a = Double.NaN;
	b = 185.5;
	c = Double.sum(a, b);
	//@ assert Double.isNaN(c);
	a = Double.POSITIVE_INFINITY;
	b = Double.POSITIVE_INFINITY;
	c = Double.sum(a, b);
	//@ assert c == Double.POSITIVE_INFINITY;
	a = Double.NEGATIVE_INFINITY;
	b = Double.NEGATIVE_INFINITY;
	c = Double.sum(a, b);
	//@ assert c == Double.NEGATIVE_INFINITY;
	a = Double.NEGATIVE_INFINITY;
	b = Double.POSITIVE_INFINITY;
	c = Double.sum(a, b);
	//@ assert Double.isNaN(c);
}


//@ requires Double.isFinite(a);
public static void sum_test_1(double a)
{
	double b = Double.sum(a, -a);
	//@ assert b == 0.0;
}


//@ requires Double.isFinite(a) && Double.isFinite(b);
public static void sum_test_2(double a, double b)
{
	double c = Double.sum(a, b);
	//@ assert c == a + b;
}

//@ requires Double.isFinite(a) && Double.isFinite(b);
public static void sum_test_3(double a, double b)
{
	double c = Double.sum(a, b);
	//@ assert (a >= 0 && b >= 0) ==> c >= 0;
	//@ assert (a <= 0 && b <= 0) ==> c <= 0;
}


public static void sum_NaN_tests(double a, double b)
{
	double c = Double.sum(Double.NaN, a);
	//@ assert Double.isNaN(c);
	c = Double.sum(a, b);
	//@ assert Double.isNaN(c) <==> (Double.isNaN(a) || Double.isNaN(b));
	c = Double.sum(Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY);
	//@ assert Double.isNaN(c);
}

public static void sum_inf_tests(double a, double b)
{
	double c = Double.sum(Double.POSITIVE_INFINITY, a);
	//@ assert Double.isInfinite(c) || Double.isNaN(c);
	c = Double.sum(Double.NEGATIVE_INFINITY, a);
	//@ assert Double.isInfinite(c) || Double.isNaN(c);
	
}


public static void min_literal_tests()
{
	double c;
	// integer inputs
	c = Double.min(31, 26);
	//@ assert c == 26.0;
	c = Double.min(-16, -23);
	//@ assert c == -23.0;
	c = Double.min(0, 0);
	//@ assert c == 0.0;
	
	// floats
	c = Double.min(0.0f, 0.0f);
	//@ assert c == 0.0;
	c = Double.min(-0.0f, -0.0f);
	//@ assert c == 0.0;
	c = Double.min(Float.POSITIVE_INFINITY, Float.POSITIVE_INFINITY);
	//@ assert c == Double.POSITIVE_INFINITY;
	c = Double.min(Float.NEGATIVE_INFINITY, Float.NEGATIVE_INFINITY);
	//@ assert c == Double.NEGATIVE_INFINITY;
	c = Double.min(Float.NaN, Float.NaN);
	//@ assert c != c;
	
	// doubles
	c = Double.min(0.0, 0.0);
	//@ assert c == 0;
	c = Double.min(-0.0, -0.0);
	//@ assert c == 0;
	c = Double.min(182.28, 582.2004);
	//@ assert c == 182.28;
	c = Double.min(-19258.4, -404.234);
	//@ assert c == -19258.4;
	c = Double.min(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);
	//@ assert c == Double.POSITIVE_INFINITY;
	c = Double.min(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY);
	//@ assert c == Double.NEGATIVE_INFINITY;
	c = Double.min(Double.NaN, Double.NaN);
	//@ assert c != c;
}


//@ requires Double.isFinite(a) && Double.isFinite(b);
public static void min_test_1(double a, double b)
{
	double c = Double.min(a, b);
	//@ assert a <= b ==> c == a;
	//@ assert b <= a ==> c == b;
}


//@ requires Double.isFinite(a) && Double.isFinite(b);
public static void min_test_2(double a, double b) 
{
        double c = Double.min(a, b);
	//@ assert c <= a && c <= b;
	//@ assert c == a || c == b;
}


//@ requires Double.isFinite(a) && Double.isFinite(b);
public static void min_test_3(double a, double b) 
{
	double c = Double.min(5 * a - 4, -2 * b + 3);
	//@ assert c <= 5*a - 4 && c <= -2*b + 3;
	//@ assert c == 5*a - 4 || c == -2*b + 3;
}


public static void min_NaN_tests(double a, double b)
{
	double c = Double.min(Double.NaN, Double.NaN);
	//@ assert Double.isNaN(c);
	
	c = Double.min(Double.NaN, a);
	//@ assert Double.isNaN(c);
	
	c = Double.min(a, b);
	//@ assert (Double.isNaN(a) || Double.isNaN(b)) ==> Double.isNaN(c);
	//@ assert (!Double.isNaN(a) && !Double.isNaN(b)) ==> !Double.isNaN(c);
}

public static void min_inf_tests(double a, double b)
{
	double c = Double.min(Double.NEGATIVE_INFINITY, a);
	//@ assert Double.isInfinite(c);
	
	c = Double.min(Double.POSITIVE_INFINITY, a);
	//@ assert Double.isFinite(a) ==> Double.isFinite(c);
	//@ assert (a > Double.NEGATIVE_INFINITY) ==> Double.isFinite(c);

	c = Double.min(a, b);
	//@ assert (Double.isFinite(a) && Double.isFinite(b)) ==> Double.isFinite(c);
	//@ assert (Double.isInfinite(a) && Double.isInfinite(b)) ==> Double.isInfinite(c);
	//@ assert Double.isInfinite(c) ==> (Double.isInfinite(a) || Double.isInfinite(b));
}


}
