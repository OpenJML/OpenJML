/*
THIS PROGRAM TESTS THE FOLLOWING METHODS FROM java.lang.Double:

Float.valueOf(float f)


*/


public class InitTests
{

	// testing Float.valueOf(float)
	public static void valueOf_literal_tests()
	{
		float a;
		Float b;

		a = Float.NaN;
		b = Float.valueOf(a);
		//@ assert b.floatValue() != b.floatValue();

		a = Float.POSITIVE_INFINITY;
		b = Float.valueOf(a);
		 //@ assert b == Float.POSITIVE_INFINITY;

		a = Float.NEGATIVE_INFINITY;
		b = Float.valueOf(a);
		 //@ assert b == Float.NEGATIVE_INFINITY;

		a = 0.0f;
		b = Float.valueOf(a);
		 //@ assert b == 0.0f;

		a = -0.0f;
		b = Float.valueOf(a);
		 //@ assert b == 0.0f;

		a = 40.56f;
		b = Float.valueOf(a);
		 //@ assert b == 40.56f;

		a = 48654683f;
		b = Float.valueOf(a);
		 //@ assert b == 48654683f;

                a = -6789.87f;
                b = Float.valueOf(a);
                 //@ assert b == -6789.87f;

                a = 0.0988767f;
                b = Float.valueOf(a);
                 //@ assert b == 0.0988767f;

		a = 0x0.000002P-126f;
		b = Float.valueOf(a);
		 //@ assert b == Float.MIN_VALUE;

		a = 0x1.fffffep127f;
		b = Float.valueOf(a);
		 //@ assert b == Float.MAX_VALUE;

		a = 0x1.0p-126f;
		b = Float.valueOf(a);
		 //@ assert b == Float.MIN_NORMAL;
		
		a = 0x1.0p0f;
		b = Float.valueOf(a);
		 //@ assert b == 1.0f;

		a = -0x1.0p0f;
		b = Float.valueOf(a);
		 //@ assert b == -1.0f;

		a = 0x1.0p1f;
		b = Float.valueOf(a);
		 //@ assert b == 2.0f;

		a = 	0x1.8p1f;
		b = Float.valueOf(a);
		 //@ assert b == 3.0f;

		a = 0x1.0p-1f;
		b = Float.valueOf(a);
		 //@ assert b == 0.5f;

		a = 0x1.0p-2f;
		b = Float.valueOf(a);
		//@ assert b == 0.25f;
		
		a = 3.1415f;
		b = Float.valueOf(a);
		//@ assert b == 3.1415f;

		a = 3f;
		b = Float.valueOf(a);
		//@ assert b == 3.0f;

	}

        public static void valueOf_NaN_tests(float a)
        {
        	Float b = Float.valueOf(a);
		//@ assert Float.isNaN(a) <==> Float.isNaN(b.floatValue());
		//@ assert Float.isNaN(a) <==> b.isNaN();
        }

        public static void valueOf_inf_tests(float a)
        {
                Float b = Float.valueOf(a);
        	//@ assert Float.isFinite(a) <==> Float.isFinite(b.floatValue());
        	//@ assert Float.isInfinite(a) <==> Float.isInfinite(b.floatValue());
		//@ assert Float.isInfinite(a) <==> b.isInfinite();
        }

}
