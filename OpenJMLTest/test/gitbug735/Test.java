// These equations prove OK for ints but need work for doubles.

public class Test {

	// @ requires Double.isFinite(a) && Double.isFinite(a*a);
	   public static void impl(double a, int b)
	   {
		   //@ assume -1000 < b < 1000;
	       // @ assert (b == 0) | ( b*b != 0);
	        // quadratic equations
		   //@ assume -1000 < a < 1000;
	       //@ assert (a == 0) | ( a*a != 0);
	       // @ assert ( a*a == 0) ==> a == 0;
	   }

	   //Original bug
	//@ requires a==a && b==b && c == c && d==d;
	   public static void implorig(double a, double b, double c, double d)
	   {
	        // quadratic equations
	        //@ assert ( (a - b) * (c - d) == 0 ) ==> (a == b || c == d);
	   }

}

class TestInt {

       public static void impl(int a)
       {
           //@ assume -1000 < a < 1000;
           //@ assert (a == 0) | ( a*a != 0);
       }

       //@ requires -1000 < a < 1000;
       //@ requires -1000 < b < 1000;
       //@ requires -1000 < c < 1000;
       //@ requires -1000 < d < 1000;
       public static void implorig(int a, int b, int c, int d)
       {
            // quadratic equations
            //@ assert ( (a - b) * (c - d) == 0 ) ==> (a == b || c == d);
       }

}
