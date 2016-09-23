public class Sqrt {

	double precision = 0.0001;

	//@ ghost public static double eps = 0.00001;

	/*@
@ requires x >= 0.0;
@ //ensures org.jmlspecs.models.JMLDouble.approximatelyEqualTo(x, \result * \result, eps);
@*/
	public double sqrt(double x) {
		double a = 0, b = x+1, m = 0;
		//@ assert b >= x;
		//@ assert x >= a;
		//@ assert b >= a;
		//@ loop_invariant b >= a;
		while (b*b - a*a > precision) {
			m = (b + a) / 2;
			if (m * m > x) {
				b = m;
			}
			else {
				a = m;
			}
			//@ assert b >= m && m >= a;
			//@ assert b >= a;
			//@ assert b*b >= m*m && m*m >= a*a;
		}
		// @ assert b >= m && m >= a;
		// @ assert b*b >= m*m && m*m >= a*a;
		return m;
	}
}
// FIXME - requires explicit AUFNIRA logic; also needs more help - current specs are invalid (e.g. b ==x does not mean b*b > x)