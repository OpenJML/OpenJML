import java.lang.Math;

public class NextDown
{

// //THE FOLLOWING TEST OF nextDown SHOULD BE VALIDATED BY OpenJML

//@ requires !Double.isNaN(a) && a != Double.NEGATIVE_INFINITY && a != Double.POSITIVE_INFINITY;
//@ ensures \result < a;
public static double nextDown_test_1(double a)
{
	double c = Math.nextDown(a);
	return c;
}


//@ requires !Double.isNaN(a) && a != Double.NEGATIVE_INFINITY && a != Double.POSITIVE_INFINITY;
//@ ensures \result == 0;
public static double nextDown_test_2(double a)
{
        double c = 0 + 0 * Math.nextDown(a);
        return c;
}



// //THE FOLLOWING TEST OF nextDown SHOULD NOT BE VALIDATED BY OpenJML

//@ requires !Double.isNaN(a) && a != Double.NEGATIVE_INFINITY && a != Double.POSITIVE_INFINITY;
//@ ensures \result >= a;
public static double nextDown_test_3(double a)
{
        double c = Math.nextDown(a);
        return c;
}

}
