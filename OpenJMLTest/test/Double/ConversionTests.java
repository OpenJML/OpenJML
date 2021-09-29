/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Double:

.shortValue()



*/


public class ConversionTests
{

//here we test the instance method Double.shortValue()
public static void shortValue_literal_tests()
{
	Double a;
	short b;

	//integers
	a = (double) 4;
	b = a.shortValue();
	//@ assert b == 4;
	a = (double) -8;
	b = a.shortValue();
	//@ assert b == -8;
	a = (double) 1834;
	b = a.shortValue();
	//@ assert b == 1834;
	
	//floats
	a = (double) 3.345f;
	b = a.shortValue();
	//@ assert b == 3;
	a = (double) -858484.34f;
	b = a.shortValue();
	//@ assert b == -6516;
	a = (double) 1834.22999f;
	b = a.shortValue();
	//@ assert b == 1834;
	
	//doubles
	a = Double.NaN;
	b = a.shortValue();
	//@ assert b == 0;
	a = Double.POSITIVE_INFINITY;
	b = a.shortValue();
	//@ assert b == -1;
	a = Double.NEGATIVE_INFINITY;
	b = a.shortValue();
	//@ assert b == 0;
	a = 3.0;
	b = a.shortValue();
	//@ assert b == 3;
	a = 493403.32;
	b = a.shortValue();
	//@ assert b == -30885;
	a = -181.381818;
	b = a.shortValue();
	//@ assert b == -181;
	a = 99.9999999;
	b = a.shortValue();
	//@ assert b == 99;
}

public static void shortValue_test_1(Double a)
{
	short b = a.shortValue();
	//@ assert b <= 32767 && b >= -32768;
}

}
