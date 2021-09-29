import java.lang.Math;
public class Random
{

	// //THE FOLLOWING TWO FUNCTIONS SHOULD BE EVALUATED AS VALID BY OPENJML

	// // OpenJML's static checker should not issue any warnings on this test
	// // Here we simply ensure that the output of the random call is >= 0 and < 1 as specified by java.lang.Math.random
	//@ ensures 0.0 <= \result  &&  \result < 1.0;
	public static double random_test_1()
	{
		double a = Math.random();
		return a;
	}

	// //This is a slightly more complicated example involving Math.random that should still evaluate to true
	//@ ensures -5.0 <= \result  &&  \result < 5.0;
        public static double random_test_2()
        {
                double a = Math.random();
		a = 10 * a;
		a = a - 5;
                return a;
        }
}
