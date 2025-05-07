public class ConstantTests
{

	public static void pos_inf_call()
	{
		double a = Double.POSITIVE_INFINITY;
	}
	
	public static void neg_inf_call()
	{
		double a = Double.NEGATIVE_INFINITY;
	}
	
	public static void nan_call()
	{
		double a = Double.NaN;
	}
	
	public static void max_value_call()
	{
		double a = Double.MAX_VALUE;
	}
	
	public static void max_value_test()
	{
		double a = Double.MAX_VALUE;
		//@ assert a == 0x1.fffffffffffffP+1023;
	}
	
	public static void min_value_call()
	{
		double a = Double.MIN_VALUE;
	}
	
	public static void min_value_test()
	{
		double a = Double.MIN_VALUE;
		//@ assert a == 0x0.0000000000001P-1022;
	}
	
	public static void min_normal_call()
	{
		double a = Double.MIN_NORMAL;
	}
	
	public static void min_normal_test()
	{
		double a = Double.MIN_NORMAL;
		//@ assert a == 0x1.0p-1022;
	}
	
	public static void bytes_call()
	{
		double a = Double.BYTES;
	}
	
	public static void bytes_test()
	{
		double a = Double.BYTES;
		//@ assert a == 8;
	}

	public static void max_exponent_call()
	{
		double a = Double.MAX_EXPONENT;
	}	

	public static void max_exponent_test()
	{
		double a = Double.MAX_EXPONENT;
		//@ assert a == 1023;
	}	
	
	public static void min_exponent_call()
	{
		double a = Double.MIN_EXPONENT;
	}
	
	public static void min_exponent_test()
	{
		double a = Double.MIN_EXPONENT;
		//@ assert a == -1022;
	}
	
	public static void size_call()
	{
		double a = Double.SIZE;
	}

	public static void size_test()
	{
		double a = Double.SIZE;
		//@ assert a == 64;
	}	

}
