/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Double:

Float.toString(float f)
Float.toHexString(float f)
Float.valueOf(String s)

*/

public class StringTests
{

//checking the static version of Float.toString(float f)
public static void toString_literal_tests()
{
	String c, d;

	// integer inputs
	c = Float.toString(31);
	d = "31.0";
	//@ assert c.equals(d);
	c = Float.toString(-23);
	d = "-23.0";
	//@ assert c.equals(d);
	c = Float.toString(0);
	d = "0.0";
	//@ assert c.equals(d);


	// floats
	c = Float.toString(0.0f);
	//@ assert c.equals(d);
	c = Float.toString(-0.0f);
	d = "-0.0";
	//@ assert c.equals(d);
	c = Float.toString(13.73f);
	d = "13.73";
	//@ assert c.equals(d);
	c = Float.toString(-12.10f);
	d = "-12.1";
	//@ assert c.equals(d);
	c = Float.toString(Float.POSITIVE_INFINITY);
	d = "Infinity";
	//@ assert c.equals(d);
	c = Float.toString(Float.NEGATIVE_INFINITY);
	d = "-Infinity";
	//@ assert c.equals(d);
	c = Float.toString(Float.NaN);
	d = "NaN";
	//@ assert c.equals(d);
}

//@ requires Float.isFinite(a);
public static void toString_test_1(float a)
{
	String c = Float.toString(a);
	//@ assert a < 0 ==> c.charAt(0) == '-';
	//@ assert c.charAt(0) == '-' ==> a <= 0;
}


public static void toString_NaN_tests(float a)
{
	String c, d;
	c = Float.toString(a);
	
	d = "NaN";
	//@ assert Float.isNaN(a) <==> c.equals(d);

}

public static void toString_inf_tests(float a)
{
	String c, d, e;
	c = Float.toString(a);
	
	d = "Infinity";
	//@ assert c.equals(d) ==> Float.isInfinite(a);
	
	e = "-Infinity";
	//@ assert c.equals(e) ==> Float.isInfinite(a);
	
	//@ assert (c.equals(d) || c.equals(e)) <==> Float.isInfinite(a);
}


//checking the instance method version of Float.toString
public static void toString_instance_literal_tests()
{
	String c, d;
	
	// integer inputs
	Float a = new Float(31);
	c = a.toString();
	d = "31.0";
	//@ assert c.equals(d);
	a = new Float(-23);
	c = a.toString();
	d = "-23.0";
	//@ assert c.equals(d);
	a = new Float(0);
	c = a.toString();
	d = "0.0";
	//@ assert c.equals(d);

	// floats
	a = new Float(0.0f);
	c = a.toString();
	//@ assert c.equals(d);
	a = new Float(-0.0f);
	c = a.toString();
	d = "-0.0";
	//@ assert c.equals(d);
	a = new Float(-13.73f);
	c = a.toString();
	d = "-13.73";
	//@ assert c.equals(d);
	a = new Float(-12.10f);
	c = a.toString();
	d = "-12.1";
	//@ assert c.equals(d);
	a = new Float(Float.POSITIVE_INFINITY);
	c = a.toString();
	d = "Infinity";
	//@ assert c.equals(d);
	a = new Float(Float.NEGATIVE_INFINITY);
	c = a.toString();
	d = "-Infinity";
	//@ assert c.equals(d);
	a = new Float(Float.NaN);
	c = a.toString();
	d = "NaN";
	//@ assert c.equals(d);
}


public static void toString_instance_NaN_tests(Float a)
{
	String c, d;
	c = a.toString();
	
	d = "NaN";
	//@ assert a.isNaN() <==> c.equals(d);
}


public static void toString_instance_inf_tests(Float a)
{
	String c, d, e;
	c = a.toString();
	
	d = "Infinity";
	//@ assert c.equals(d) ==> a.isInfinite();
	
	e = "-Infinity";
	//@ assert c.equals(e) ==> a.isInfinite();
	
	//@ assert (c.equals(d) || c.equals(e)) <==> a.isInfinite();
}



//checking Float.toHexString(float f)
public static void toHexString_literal_tests()
{
	String c, d;
	
	// integer inputs
	c = Float.toHexString(0);
	d = "0x0.0p0";
	//@ assert c.equals(d);

	// floats
	c = Float.toHexString(0.0f);
	//@ assert c.equals(d);
	c = Float.toHexString(-0.0f);
	d = "-0x0.0p0";
	//@ assert c.equals(d);
	c = Float.toHexString(1.0f);
	d = "0x1.0p0";
	//@ assert c.equals(d);
	c = Float.toHexString(-1.0f);
	d = "-0x1.0p0";
	//@ assert c.equals(d);
	c = Float.toHexString(2.0f);
	d = "0x1.0p1";
	//@ assert c.equals(d);
	c = Float.toHexString(3.0f);
	d = "0x1.8p1";
	//@ assert c.equals(d);
	c = Float.toHexString(0.5f);
	d = "0x1.0p-1";
	//@ assert c.equals(d);
	c = Float.toHexString(0.25f);
	d = "0x1.0p-2";
	//@ assert c.equals(d);
	c = Float.toHexString(Float.MAX_VALUE);
	d = "0x1.fffffep127";
	//@ assert c.equals(d);
	c = Float.toHexString(Float.MIN_VALUE);
	d = "0x0.000002p-126";
	//@ assert c.equals(d);
	c = Float.toHexString(Float.POSITIVE_INFINITY);
	d = "Infinity";
	//@ assert c.equals(d);
	c = Float.toHexString(Float.NEGATIVE_INFINITY);
	d = "-Infinity";
	//@ assert c.equals(d);
	c = Float.toHexString(Float.NaN);
	d = "NaN";
	//@ assert c.equals(d);
}


//@ requires Float.isFinite(a);
public static void toHexString_test_1(float a)
{
	String c = Float.toHexString(a);
	//@ assert a < 0 ==> c.charAt(0) == '-';
	//@ assert c.charAt(0) == '-' ==> a <= 0;
}


public static void toHexString_NaN_tests(float a)
{
	String c, d;
	c = Float.toHexString(a);
	d = "NaN";
	//@ assert Float.isNaN(a) <==> c.equals(d);
}


public static void toHexString_inf_tests(float a)
{
	String c, d, e;
	c = Float.toHexString(a);
	
	d = "Infinity";
	//@ assert c.equals(d) ==> Float.isInfinite(a);
	
	e = "-Infinity";
	//@ assert c.equals(e) ==> Float.isInfinite(a);
	
	//@ assert (c.equals(d) || c.equals(e)) <==> Float.isInfinite(a);
}


	//testing Float.valueOf(String a)

public static void valueOf_string_literal_tests()
{
	String a;
	Float b;

	a = "NaN";
	b = Float.valueOf(a);
	 //@ assert b.floatValue() != b.floatValue();

	a = "Infinity";
	b = Float.valueOf(a);
	 //@ assert b == Float.POSITIVE_INFINITY;

	a = "-Infinity";
	b = Float.valueOf(a);
	 //@ assert b == Float.NEGATIVE_INFINITY;

	a = "0.0";
	b = Float.valueOf(a);
	//@ assert b == 0.0f;

	a = " \t \n   0.0   \n\n\t   ";
	b = Float.valueOf(a);
	//@ assert b == 0.0f;

	a = "40.56";
	b = Float.valueOf(a);
	//@ assert b == 40.56f;

	a = "48654683";
	b = Float.valueOf(a);
	//@ assert b == 48654683f;

	a = "-6789.87";
	b = Float.valueOf(a);
	//@ assert b == -6789.87f;

	a = "0.0988767";
	b = Float.valueOf(a);
	//@ assert b == 0.0988767f;

	a = "0x0.000002P-126f";
	b = Float.valueOf(a);
	//@ assert b == Float.MIN_VALUE;

	a = "0x1.fffffep127";
	b = Float.valueOf(a);
	//@ assert b == Float.MAX_VALUE;

	a = "0x1.0p-126f";
	b = Float.valueOf(a);
	//@ assert b == Float.MIN_NORMAL;
		
	a = "	0x1.0p0";
	b = Float.valueOf(a);
	//@ assert b == 1.0f;

	a = "-0x1.0p0";
	b = Float.valueOf(a);
	//@ assert b == -1.0f;

	a = "0x1.0p1";
	b = Float.valueOf(a);
	//@ assert b == 2.0f;

	a = "	0x1.8p1";
	b = Float.valueOf(a);
	//@ assert b == 3.0f;

	a = "0x1.0p-1";
	b = Float.valueOf(a);
	//@ assert b == 0.5f;

	a = "0x1.0p-2";
	b = Float.valueOf(a);
	//@ assert b == 0.25f;
		 
	a = "1";
	b = Float.valueOf(a);
	//@ assert b == 1.0f;
	 
	a = "3.1415f";
	b = Float.valueOf(a);
	//@ assert b == 3.1415f;
}

public static void valueOf_string_NaN_tests(String a)
{
	Float b = Float.valueOf(a);
	String c = "NaN";
	//@ assert c.equals(a.trim()) ==> b.floatValue() != b.floatValue();
}

public static void valueOf_string_inf_tests(String a)
{
	Float b = Float.valueOf(a);
	String c = "Infinity";
	//@ assert c.equals(a.trim()) ==> b.floatValue() == Float.POSITIVE_INFINITY;
	b = Float.valueOf(a);
	c = "-Infinity";
	//@ assert c.equals(a.trim()) ==> b.floatValue() == Float.NEGATIVE_INFINITY;
}




}
