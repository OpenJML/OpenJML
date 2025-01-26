public class ConstantTests
{

	public static void pos_inf_call()
	{
		float a = Float.POSITIVE_INFINITY;
	}
	
	public static void neg_inf_call()
	{
		float a = Float.NEGATIVE_INFINITY;
	}
	
	public static void nan_call()
	{
		float a = Float.NaN;
	}
	
	public static void max_value_call()
	{
		float a = Float.MAX_VALUE;
	}
	
	public static void max_value_test()
	{
		float a = Float.MAX_VALUE;
		//@ assert a == 0x1.fffffeP+127f;
	}
	
	public static void min_value_call()
	{
		float a = Float.MIN_VALUE;
	}
	
	public static void min_value_test()
	{
		float a = Float.MIN_VALUE;
		//@ assert a == 0x0.000002P-126f;
	}
	
	public static void min_normal_call()
	{
		float a = Float.MIN_NORMAL;
	}
	
	public static void min_normal_test()
	{
		float a = Float.MIN_NORMAL;
		//@ assert a == 0x1.0p-126f;
	}
	
	public static void bytes_call()
	{
		float a = Float.BYTES;
	}
	
	public static void bytes_test()
	{
		float a = Float.BYTES;
		//@ assert a == 4;
	}

	public static void max_exponent_call()
	{
		float a = Float.MAX_EXPONENT;
	}	

	public static void max_exponent_test()
	{
		float a = Float.MAX_EXPONENT;
		//@ assert a == 127;
	}	
	
	public static void min_exponent_call()
	{
		float a = Float.MIN_EXPONENT;
	}
	
	public static void min_exponent_test()
	{
		float a = Float.MIN_EXPONENT;
		//@ assert a == -126;
	}
	
	public static void size_call()
	{
		float a = Float.SIZE;
	}

	public static void size_test()
	{
		float a = Float.SIZE;
		//@ assert a == 32;
	}	

}
