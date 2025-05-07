public class Cbrt
{
  //@ requires Double.isFinite(a);
	public static void cbrtTest(double a)
	{
		double result = Math.cbrt(a);
		//@ assert Double.isFinite(result);
		//@ assert Math.close(a, result * result * result, 3.0E-16);
	}

	//@ requires ! Double.isFinite(a);
	public static void cbrtTestAnomalies(double a)
	{
		double result = Math.cbrt(a);
		//@ assert Double.isNaN(a) ==> Double.isNaN(result);
		//@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, Double.POSITIVE_INFINITY) == 0);
		//@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, Double.NEGATIVE_INFINITY) == 0);
	}
}
