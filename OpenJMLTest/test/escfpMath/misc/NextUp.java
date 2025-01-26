import java.lang.Math;

public class NextUp
{

// //THE FOLLOWING TEST OF nextUp SHOULD BE VALIDATED BY OpenJML

//@ requires !Double.isNaN(a) && a != Double.NEGATIVE_INFINITY && a != Double.POSITIVE_INFINITY;
//@ ensures \result > a;
public static double nextUp_test_1(double a)
{
	double c = Math.nextUp(a);
	return c;
}


//@ requires !Double.isNaN(a) && a != Double.NEGATIVE_INFINITY && a != Double.POSITIVE_INFINITY;
//@ ensures \result == 0;
public static double nextUp_test_2(double a)
{
        double c = 0 + 0 * Math.nextUp(a);
        return c;
}



// //THE FOLLOWING TEST OF nextUp SHOULD NOT BE VALIDATED BY OpenJML

//@ requires !Double.isNaN(a) && a != Double.NEGATIVE_INFINITY && a != Double.POSITIVE_INFINITY;
//@ ensures \result >= a;
public static double nextUp_test_3(double a)
{
        double c = Math.nextUp(a);
        return c;
}

}
