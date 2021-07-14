public class Test {
	
	public static void m() {
		//@ assert (double)12345678 == 12345678.0;
		//@ assert 1.2345678e7 == 12345678.0;
		//@ assert 1.2345670e7 == 12345670.0;
		//@ assert 9.99999e-7 == 0.000000999999;
		//@ assert 38.5E-8 == 38.5E-8;
		//@ assert 3.85E-7 == 3.85E-7;
	}
}