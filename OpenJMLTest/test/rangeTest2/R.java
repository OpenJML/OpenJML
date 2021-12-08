public class R {

//@ ghost public static range r = 2 ..3 ;

//@ writes a[r];
void m(int[] a) {
 //@ set var rr = r;
 //@ set var k = r.lo;
}
}
