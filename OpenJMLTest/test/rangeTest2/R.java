public class R {

	//@ ghost public static range r = 2 ..3 ;

	//@ writes a[r];
	void m(int[] a) {
		//@ ghost var rr = r;
		//@ ghost var k = r.lo;
		//@ set r.lo = 5;
	}
}
