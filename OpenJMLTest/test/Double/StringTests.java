/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Double:

Double.toString(double d)

Double.toHexString(double d)

Double.parseDouble(String s)

Double.valueOf(String s);

*/


public class StringTests
{

//here we test the static method Double.toString(double d)

public static void toString_literal_tests()
{
	String c, d;

	// integer inputs
	c = Double.toString(31);
	d = "31.0";
	//@ assert c.equals(d);
	c = Double.toString(-23);
	d = "-23.0";
	//@ assert c.equals(d);
	c = Double.toString(0);
	d = "0.0";
	//@ assert c.equals(d);


	// floats
	c = Double.toString(0.0f);
	//@ assert c.equals(d);
	c = Double.toString(-0.0f);
	d = "-0.0";
	//@ assert c.equals(d);
	c = Double.toString(Float.POSITIVE_INFINITY);
	d = "Infinity";
	//@ assert c.equals(d);
	c = Double.toString(Float.NEGATIVE_INFINITY);
	d = "-Infinity";
	//@ assert c.equals(d);
	c = Double.toString(Float.NaN);
	d = "NaN";
	//@ assert c.equals(d);
	
	// doubles
	c = Double.toString(0.0);
	d = "0.0";
	//@ assert c.equals(d);
	c = Double.toString(-0.0);
	d = "-0.0";
	//@ assert c.equals(d);
	c = Double.toString(13.73);
	d = "13.73";
	//@ assert c.equals(d);
	c = Double.toString(-12.10);
	d = "-12.1";
	//@ assert c.equals(d);
	c = Double.toString(Double.POSITIVE_INFINITY);
	d = "Infinity";
	//@ assert c.equals(d);
	c = Double.toString(Double.NEGATIVE_INFINITY);
	d = "-Infinity";
	//@ assert c.equals(d);
	c = Double.toString(Double.NaN);
	d = "NaN";
	//@ assert c.equals(d);
}

//@ requires Double.isFinite(a);
public static void toString_test_1(double a)
{
	String c = Double.toString(a);
	//@ assert a < 0 ==> c.charAt(0) == '-';
	//@ assert c.charAt(0) == '-' ==> a <= 0;
}


public static void toString_NaN_tests(double a)
{
	String c, d;
	c = Double.toString(a);
	
	d = "NaN";
	//@ assert Double.isNaN(a) <==> c.equals(d);

}

public static void toString_inf_tests(double a)
{
	String c, d, e;
	c = Double.toString(a);
	
	d = "Infinity";
	//@ assert c.equals(d) ==> Double.isInfinite(a);
	
	e = "-Infinity";
	//@ assert c.equals(e) ==> Double.isInfinite(a);
	
	//@ assert (c.equals(d) || c.equals(e)) <==> Double.isInfinite(a);
}


//now we check the instance method version of Double.toString

public static void toString_instance_literal_tests()
{
	String c, d;
	
	// integer inputs
	Double a = new Double(31);
	c = a.toString();
	d = "31.0";
	//@ assert c.equals(d);
	a = new Double(-23);
	c = a.toString();
	d = "-23.0";
	//@ assert c.equals(d);
	a = new Double(0);
	c = a.toString();
	d = "0.0";
	//@ assert c.equals(d);

	// floats
	a = new Double(0.0f);
	c = a.toString();
	//@ assert c.equals(d);
	a = new Double(-0.0f);
	c = a.toString();
	d = "-0.0";
	//@ assert c.equals(d);
	a = new Double(Float.POSITIVE_INFINITY);
	c = a.toString();
	d = "Infinity";
	//@ assert c.equals(d);
	a = new Double(Float.NEGATIVE_INFINITY);
	c = a.toString();
	d = "-Infinity";
	//@ assert c.equals(d);
	a = new Double(Float.NaN);
	c = a.toString();
	d = "NaN";
	//@ assert c.equals(d);
	
	// doubles
	a = new Double(0.0);
	c = a.toString();
	d = "0.0";
	//@ assert c.equals(d);
	a = new Double(-0.0);
	c = a.toString();
	d = "-0.0";
	//@ assert c.equals(d);
	a = new Double(-13.73);
	c = a.toString();
	d = "-13.73";
	//@ assert c.equals(d);
	a = new Double(-12.10);
	c = a.toString();
	d = "-12.1";
	//@ assert c.equals(d);
	a = new Double(Double.POSITIVE_INFINITY);
	c = a.toString();
	d = "Infinity";
	//@ assert c.equals(d);
	a = new Double(Double.NEGATIVE_INFINITY);
	c = a.toString();
	d = "-Infinity";
	//@ assert c.equals(d);
	a = new Double(Double.NaN);
	c = a.toString();
	d = "NaN";
	//@ assert c.equals(d);
}


public static void toString_instance_NaN_tests(Double a)
{
	String c, d;
	c = a.toString();
	
	d = "NaN";
	//@ assert a.isNaN() <==> c.equals(d);
}


public static void toString_instance_inf_tests(Double a)
{
	String c, d, e;
	c = a.toString();
	
	d = "Infinity";
	//@ assert c.equals(d) ==> a.isInfinite();
	
	e = "-Infinity";
	//@ assert c.equals(e) ==> a.isInfinite();
	
	//@ assert (c.equals(d) || c.equals(e)) <==> a.isInfinite();
}


//here we test Double.toHexString(double d)

public static void toHexString_literal_tests()
{
	String c, d;
	
	// integer inputs
	c = Double.toHexString(0);
	d = "0x0.0p0";
	//@ assert c.equals(d);

	// floats
	c = Double.toHexString(0.0f);
	//@ assert c.equals(d);
	c = Double.toHexString(-0.0f);
	d = "-0x0.0p0";
	//@ assert c.equals(d);
	c = Double.toHexString(1.0f);
	d = "0x1.0p0";
	//@ assert c.equals(d);
	c = Double.toHexString(-1.0f);
	d = "-0x1.0p0";
	//@ assert c.equals(d);
	c = Double.toHexString(2.0f);
	d = "0x1.0p1";
	//@ assert c.equals(d);
	c = Double.toHexString(3.0f);
	d = "0x1.8p1";
	//@ assert c.equals(d);
	c = Double.toHexString(0.5f);
	d = "0x1.0p-1";
	//@ assert c.equals(d);
	c = Double.toHexString(0.25f);
	d = "0x1.0p-2";
	//@ assert c.equals(d);
	
	// doubles
	c = Double.toHexString(Double.MAX_VALUE);
	d = "0x1.fffffffffffffp1023";
	//@ assert c.equals(d);
	c = Double.toHexString(Double.MIN_VALUE);
	d = "0x0.0000000000001p-1022";
	//@ assert c.equals(d);
	c = Double.toHexString(Double.POSITIVE_INFINITY);
	d = "Infinity";
	//@ assert c.equals(d);
	c = Double.toHexString(Double.NEGATIVE_INFINITY);
	d = "-Infinity";
	//@ assert c.equals(d);
	c = Double.toHexString(Double.NaN);
	d = "NaN";
	//@ assert c.equals(d);
	c = Double.toHexString(0.0);
	d = "0x0.0p0";
	//@ assert c.equals(d);
	c = Double.toHexString(-0.0);
	d = "-0x0.0p0";
	//@ assert c.equals(d);
	c = Double.toHexString(1.0);
	d = "0x1.0p0";
	//@ assert c.equals(d);
	c = Double.toHexString(-1.0);
	d = "-0x1.0p0";
	//@ assert c.equals(d);
	c = Double.toHexString(2.0);
	d = "0x1.0p1";
	//@ assert c.equals(d);
	c = Double.toHexString(3.0);
	d = "0x1.8p1";
	//@ assert c.equals(d);
	c = Double.toHexString(0.5);
	d = "0x1.0p-1";
	//@ assert c.equals(d);
	c = Double.toHexString(0.25);
	d = "0x1.0p-2";
	//@ assert c.equals(d);
}


//@ requires Double.isFinite(a);
public static void toHexString_test_1(double a)
{
	String c = Double.toHexString(a);
	//@ assert a < 0 ==> c.charAt(0) == '-';
	//@ assert c.charAt(0) == '-' ==> a <= 0;
}


public static void toHexString_NaN_tests(double a)
{
	String c, d;
	c = Double.toHexString(a);
	d = "NaN";
	//@ assert Double.isNaN(a) <==> c.equals(d);
}


public static void toHexString_inf_tests(double a)
{
	String c, d, e;
	c = Double.toHexString(a);
	
	d = "Infinity";
	//@ assert c.equals(d) ==> Double.isInfinite(a);
	
	e = "-Infinity";
	//@ assert c.equals(e) ==> Double.isInfinite(a);
	
	//@ assert (c.equals(d) || c.equals(e)) <==> Double.isInfinite(a);
}


//here we test Double.parseDouble(string s)
public static void parseDouble_string_literal_tests()
{
	String a;
	Double b;

	a = "NaN";
	b = Double.parseDouble(a);
	//@ assert b.doubleValue() != b.doubleValue();

	a = "Infinity";
	b = Double.parseDouble(a);
	 //@ assert b == Double.POSITIVE_INFINITY;

	a = "-Infinity";
	b = Double.parseDouble(a);
	 //@ assert b == Double.NEGATIVE_INFINITY;

	a = "0.0";
	b = Double.parseDouble(a);
	 //@ assert b == 0.0;

	a = " \t \n   0.0   \n\n\t   ";
	b = Double.parseDouble(a);
	 //@ assert b == 0.0;

	a = "40.56";
	b = Double.parseDouble(a);
	 //@ assert b == 40.56;

	a = "48654683";
	b = Double.parseDouble(a);
	 //@ assert b == 48654683;

	a = "-6789.87";
	b = Double.parseDouble(a);
	//@ assert b == -6789.87;

	a = "0.0988767";
	b = Double.parseDouble(a);
	//@ assert b == 0.0988767;

	a = "0x0.0000000000001p-1022";
	b = Double.parseDouble(a);
	//@ assert b == Double.MIN_VALUE;

	a = "0x1.fffffffffffffp1023";
	b = Double.parseDouble(a);
	//@ assert b == Double.MAX_VALUE;

	a = "0x1.0p-1022";
	b = Double.parseDouble(a);
	//@ assert b == Double.MIN_NORMAL;
		
	a = "	0x1.0p0";
	b = Double.parseDouble(a);
	//@ assert b == 1.0;

	a = "-0x1.0p0";
	b = Double.parseDouble(a);
	//@ assert b == -1.0;

	a = "0x1.0p1";
	b = Double.parseDouble(a);
	//@ assert b == 2.0;

	a = "	0x1.8p1";
	b = Double.parseDouble(a);
	//@ assert b == 3.0;

	a = "0x1.0p-1";
	b = Double.parseDouble(a);
	//@ assert b == 0.5;

	a = "0x1.0p-2";
	b = Double.parseDouble(a);
	//@ assert b == 0.25;
		 
	a = "3.1415f";
	b = Double.parseDouble(a);
	//@ assert b == 3.1415;
		
	a = "3";
	b = Double.parseDouble(a);
	//@ assert b == 3.0;
}


public static void parseDouble_string_NaN_tests(String a)
{
	Double b = Double.parseDouble(a);
	String c = "NaN";
	//@ assert c.equals(a.trim()) ==> b.doubleValue() != b.doubleValue();
}

public static void parseDouble_string_inf_tests(String a)
{
	Double b = Double.parseDouble(a);
	String c = "Infinity";
	//@ assert c.equals(a.trim()) ==> b.doubleValue() == Double.POSITIVE_INFINITY;

	b = Double.parseDouble(a);
	c = "-Infinity";
	//@ assert c.equals(a.trim()) ==> b.doubleValue() == Double.NEGATIVE_INFINITY;
}


     
        
// testing Double.valueOf(String a)	
public static void valueOf_string_literal_tests()
{
	String a;
	Double b;

	a = "NaN";
	b = Double.valueOf(a);
	//@ assert b.doubleValue() != b.doubleValue();

	a = "Infinity";
	b = Double.valueOf(a);
	//@ assert b == Double.POSITIVE_INFINITY;

	a = "-Infinity";
	b = Double.valueOf(a);
	//@ assert b == Double.NEGATIVE_INFINITY;

	a = "0.0";
	b = Double.valueOf(a);
	//@ assert b == 0.0;

	a = " \t \n   0.0   \n\n\t   ";
	b = Double.valueOf(a);
	//@ assert b == 0.0;

	a = "40.56";
	b = Double.valueOf(a);
	 //@ assert b == 40.56;

	a = "48654683";
	b = Double.valueOf(a);
	 //@ assert b == 48654683;

        a = "-6789.87";
        b = Double.valueOf(a);
        //@ assert b == -6789.87;

        a = "0.0988767";
        b = Double.valueOf(a);
        //@ assert b == 0.0988767;

	a = "0x0.0000000000001p-1022";
	b = Double.valueOf(a);
	 //@ assert b == Double.MIN_VALUE;

	a = "0x1.fffffffffffffp1023";
	b = Double.valueOf(a);
	 //@ assert b == Double.MAX_VALUE;

	a = "0x1.0p-1022";
	b = Double.valueOf(a);
	 //@ assert b == Double.MIN_NORMAL;
		
	a = "	0x1.0p0";
	b = Double.valueOf(a);
	 //@ assert b == 1.0;

	a = "-0x1.0p0";
	b = Double.valueOf(a);
	 //@ assert b == -1.0;

	a = "0x1.0p1";
	b = Double.valueOf(a);
	 //@ assert b == 2.0;

	a = "	0x1.8p1";
	b = Double.valueOf(a);
	 //@ assert b == 3.0;

	a = "0x1.0p-1";
	b = Double.valueOf(a);
	 //@ assert b == 0.5;

	a = "0x1.0p-2";
	b = Double.valueOf(a);
	 //@ assert b == 0.25;
		 
	a = "3.1415f";
	b = Double.valueOf(a);
	//@ assert b == 3.1415;
		
	a = "3";
	b = Double.valueOf(a);
	//@ assert b == 3.0;
}


public static void valueOf_string_NaN_tests(String a)
{
	Double b = Double.valueOf(a);
	String c = "NaN";
	//@ assert c.equals(a.trim()) ==> b.doubleValue() != b.doubleValue();
}

public static void valueOf_string_inf_tests(String a)
{
	Double b = Double.valueOf(a);
	String c = "Infinity";
	//@ assert c.equals(a.trim()) ==> b.doubleValue() == Double.POSITIVE_INFINITY;

	b = Double.valueOf(a);
	c = "-Infinity";
	//@ assert c.equals(a.trim()) ==> b.doubleValue() == Double.NEGATIVE_INFINITY;
}



}
