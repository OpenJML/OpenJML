public class CbrtTest
{
  //@ requires Double.isFinite(a);
	public static void cbrtTest(double a)
	{
		double result = Math.cbrt(a);
		//@ assert Double.isFinite(result);
		//@ assert Math.close(a, result * result * result, 3.0E-16);
	}
}
