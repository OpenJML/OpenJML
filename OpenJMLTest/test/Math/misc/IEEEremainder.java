import java.lang.Math;

public class IEEEremainder
{

// //THE FOLLOWING THREE TESTS OF IEEEremainder SHOULD BE VALIDATED BY OpenJML

//@ requires a >= 0 && b >= 0;
//@ ensures \result >= 0;
public static double IEEEremainder_test_1(double a, double b)
{
	double c = Math.IEEEremainder(a, b);
	return c;
}

//@ requires a == b;
//@ ensures \result == 0;
public static double IEEEremainder_test_2(double a, double b)
{
  double c = Math.IEEEremainder(a, b);
	return c;
}



//@ requires a > 0 && b < 0;
//@ ensures \result < 0;
public static double IEEEremainder_test_3(double a, double b)
{
        double c = Math.IEEEremainder(a, b);
        return c;
}

}
