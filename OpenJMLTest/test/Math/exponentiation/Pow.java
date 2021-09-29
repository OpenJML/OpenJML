public class Pow
{
  // TODO - make more cases for pow
	//@ requires Double.isFinite(a) && Double.isFinite(b);
	public static void powTest(double a, double b)
	{
		double result = Math.pow(a, b);
		//@ assert Double.isFinite(result);
	}
}
