public class CopySign
{
  /**
	 * Does not get anomaly testing due to either/or behavior with NaN
	 * See: https://docs.oracle.com/javase/8/docs/api/java/lang/Math.html#copySign-float-float-
	 */
	//@ requires Double.isFinite(magnitude) && Double.isFinite(sign);
	public static void copySignTestFloat(float magnitude, float sign)
	{
		float result = Math.copySign(magnitude, sign);
		//@ assert Double.isFinite(result);
		//@ assert (sign < 0.0f) && (magnitude > 0.0f) ==> (Float.compare(magnitude, result) == 0);
		//@ assert (sign < 0.0f) && (magnitude < 0.0f) ==> (Float.compare(magnitude, result) == 0);
		//@ assert (sign > 0.0f) && (magnitude < 0.0f) ==> (Float.compare(-magnitude, result) == 0);
		//@ assert (sign > 0.0f) && (magnitude > 0.0f) ==> (Float.compare(magnitude, result) == 0);
	}

	/**
	 * Does not get anomaly testing due to either/or behavior with NaN.
	 * See: https://docs.oracle.com/javase/8/docs/api/java/lang/Math.html#copySign-double-double-
	 */
	//@ requires Double.isFinite(magnitude) && Double.isFinite(sign);
	public static void copySignTestDouble(double magnitude, double sign)
	{
		double result = Math.copySign(magnitude, sign);
		//@ assert Double.isFinite(result);
		//@ assert (sign < 0.0) && (magnitude > 0.0) ==> (Double.compare(magnitude, result) == 0);
		//@ assert (sign < 0.0) && (magnitude < 0.0) ==> (Double.compare(magnitude, result) == 0);
		//@ assert (sign > 0.0) && (magnitude < 0.0) ==> (Double.compare(-magnitude, result) == 0);
		//@ assert (sign > 0.0) && (magnitude > 0.0) ==> (Double.compare(magnitude, result) == 0);
	}

}
