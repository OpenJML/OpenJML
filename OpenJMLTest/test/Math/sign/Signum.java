public class Signum
{
  /**
   * @requires Math.isFinite(num)
   * @result num > 0.0f ==> \result == 1.0f;
   * @result num < -0.0f ==> \result == -1.0f;
   */
  public static float sigNumFloat(float num)
  {
    return Math.signum(num);
  }

  /**
   * @ensures \result == Float.NaN;
   */
  public static float sigNumFloatNaN()
  {
    return Math.signum(Float.NaN);
  }

  /**
   * @ensures \result == -0.0f;
   */
  public static float sigNumFloatNegativeZero()
  {
    return Math.signum(-0.0f);
  }

  /**
   * @ensures \result == 0.0f;
   */
  public static float sigNumFloatPositiveZero()
  {
    return Math.signum(0.0f);
  }

  /**
   * @requires Math.isFinite(num)
   * @result num > 0.0 ==> \result == 1.0;
   * @result num < -0.0 ==> \result == -1.0;
   */
  public static double sigNumDouble(double num)
  {
    return Math.signum(num);
  }

  /**
   * @ensures \result == Double.NaN;
   */
  public static double sigNumDoubleNaN()
  {
    return Math.signum(Double.NaN);
  }

  /**
   * @ensures \result == -0.0f;
   */
  public static double sigNumDoubleNegativeZero()
  {
    return Math.signum(-0.0);
  }

  /**
   * @ensures \result == 0.0f;
   */
  public static double sigNumDoublePositiveZero()
  {
    return Math.signum(0.0);
  }

  //@ requires Double.isFinite(a);
	public static void signumTestFloat(float a)
	{
		float result = Math.signum(a);
		//@ assert Double.isFinite(result);
		//@ assert (Float.compare(a, 0.0f) == 0) ==> (Float.compare(result, 0.0f) == 0);
		//@ assert (Float.compare(a, -0.0f) == 0) ==> (Float.compare(result, -0.0f) == 0);
		//@ assert (a < 0.0f) ==> (Float.compare(result, -1.0f) == 0);
		//@ assert (a > 0.0f) ==> (Float.compare(result, 1.0f) == 0);
	}

	//@ requires ! Double.isFinite(a);
	public static void signumTestAnomaliesFloat(float a)
	{
		float result = Math.signum(a);
		//@ assert Float.isNaN(a) ==> Float.isNaN(result);
		//@ assert (Float.compare(a, Float.POSITIVE_INFINITY) == 0) ==> (Float.compare(result, Float.POSITIVE_INFINITY) == 0);
		//@ assert (Float.compare(a, Float.NEGATIVE_INFINITY) == 0) ==> (Float.compare(result, Float.NEGATIVE_INFINITY) == 0);
	}

	//@ requires Double.isFinite(a);
	public static void signumTestDouble(double a)
	{
		double result = Math.signum(a);
		//@ assert Double.isFinite(result);
		//@ assert (Double.compare(a, 0.0) == 0) ==> (Double.compare(result, 0.0) == 0);
		//@ assert (Double.compare(a, -0.0) == 0) ==> (Double.compare(result, -0.0) == 0);
		//@ assert (a < 0.0) ==> (Double.compare(result, -1.0) == 0);
		//@ assert (a > 0.0) ==> (Double.compare(result, 1.0) == 0);
	}

	//@ requires ! Double.isFinite(a);
	public static void signumTestAnomaliesDouble(double a)
	{
		double result = Math.signum(a);
		//@ assert Double.isNaN(a) ==> Double.isNaN(result);
		//@ assert (Double.compare(a, Double.POSITIVE_INFINITY) == 0) ==> (Double.compare(result, Double.POSITIVE_INFINITY) == 0);
		//@ assert (Double.compare(a, Double.NEGATIVE_INFINITY) == 0) ==> (Double.compare(result, Double.NEGATIVE_INFINITY) == 0);
	}
}
