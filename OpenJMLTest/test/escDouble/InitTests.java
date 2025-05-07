/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Double:

Double.valueOf(double d)


*/

public class InitTests
{

	// testing Double.valueOf(double)
	public static void valueOf_literal_tests()
	{
		double a;
		Double b;

		a = Double.NaN;
		b = Double.valueOf(a);
		//@ assert b.doubleValue() != b.doubleValue();

		a = Double.POSITIVE_INFINITY;
		b = Double.valueOf(a);
		 //@ assert b == Double.POSITIVE_INFINITY;

		a = Double.NEGATIVE_INFINITY;
		b = Double.valueOf(a);
		 //@ assert b == Double.NEGATIVE_INFINITY;

		a = 0.0;
		b = Double.valueOf(a);
		 //@ assert b == 0.0;

		a = -0.0;
		b = Double.valueOf(a);
		 //@ assert b == 0.0;

		a = 40.56;
		b = Double.valueOf(a);
		 //@ assert b == 40.56;

		a = 48654683;
		b = Double.valueOf(a);
		 //@ assert b == 48654683;

                a = -6789.87;
                b = Double.valueOf(a);
                 //@ assert b == -6789.87;

                a = 0.0988767;
                b = Double.valueOf(a);
                 //@ assert b == 0.0988767;

		a = 0x0.0000000000001p-1022;
		b = Double.valueOf(a);
		 //@ assert b == Double.MIN_VALUE;

		a = 0x1.fffffffffffffp1023;
		b = Double.valueOf(a);
		 //@ assert b == Double.MAX_VALUE;

		a = 0x1.0p-1022;
		b = Double.valueOf(a);
		 //@ assert b == Double.MIN_NORMAL;
		
		a = 0x1.0p0;
		b = Double.valueOf(a);
		 //@ assert b == 1.0;

		a = -0x1.0p0;
		b = Double.valueOf(a);
		 //@ assert b == -1.0;

		a = 0x1.0p1;
		b = Double.valueOf(a);
		 //@ assert b == 2.0;

		a = 	0x1.8p1;
		b = Double.valueOf(a);
		 //@ assert b == 3.0;

		a = 0x1.0p-1;
		b = Double.valueOf(a);
		 //@ assert b == 0.5;

		a = 0x1.0p-2;
		b = Double.valueOf(a);
		//@ assert b == 0.25;

		a = 3.1415f;
		b = Double.valueOf(a);
		//@ assert b == 3.1415f;
		
		a = 3;
		b = Double.valueOf(a);
		//@ assert b == 3.0;

	}

        public static void valueOf_NaN_tests(double a)
        {
        	Double b = Double.valueOf(a);
		//@ assert Double.isNaN(a) <==> Double.isNaN(b.doubleValue());
		//@ assert Double.isNaN(a) <==> b.isNaN();
        }

        public static void valueOf_inf_tests(double a)
        {
                Double b = Double.valueOf(a);
        	//@ assert Double.isFinite(a) <==> Double.isFinite(b.doubleValue());
        	//@ assert Double.isInfinite(a) <==> Double.isInfinite(b.doubleValue());
		//@ assert Double.isInfinite(a) <==> b.isInfinite();
        }

}
