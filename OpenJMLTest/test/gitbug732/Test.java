import java.lang.Math;
public class Test
{
	public static void copySign_test()
	{
		int a = (int)Math.copySign(64, -128);
		//@ assert a == -64;
	}
	public static void copySign_float()
	{
		float a = Math.copySign(64, -128);
		//@ assert a == -64.0;
	}
	public static void copySign_double()
	{
		double a = Math.copySign(64, -128);
		//@ assert a == -64.0;
	}	
	public static void copySign_double1()
	{
		double a = Math.copySign(-64, -128);
		//@ assert a == -64.0;
	}
	
	public static void copySign_double2()
	{
		double a = Math.copySign(64, 128);
		//@ assert a == 64.0;
	}
	
	public static void copySign_double3()
	{
		double a = Math.copySign(-64, -128);
		//@ assert a == -64.0;
	}
	public static void copySign_double0d()
	{
		double a = Math.copySign(64.0, -128.0);
		//@ assert a == -64.0;
	}	
	public static void copySign_double1d()
	{
		double a = Math.copySign(-64.0, -128.0);
		//@ assert a == -64.0;
	}
	
	public static void copySign_double2d()
	{
		double a = Math.copySign(64.0, 128.0);
		//@ assert a == 64.0;
	}
	
	public static void copySign_double3d()
	{
		double a = Math.copySign(-64.0, -128.0);
		//@ assert a == -64.0;
	}
	

}

// This test has some problem with converting or rounding float/double values

