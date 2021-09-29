import java.lang.Math;

public class NextAfter
{

// //THE FOLLOWING THREE TESTS OF nextAfter SHOULD BE VALIDATED BY OpenJML

//@ requires b > a;
//@ ensures \result > a;
public static double nextAfter_test_1(double a, double b)
{
	double c = Math.nextAfter(a, b);
	return c;
}

//@ ensures \result == 0;
public static double nextAfter_test_2(double a, double b)
{
        double c = Math.nextAfter(a, b);
	return 0 + c * 0;
}



//@ requires a > b;
//@ ensures \result < a;
public static double nextAfter_test_3(double a, double b)
{
        double c = Math.nextAfter(a, b);
        return c;
}

}
