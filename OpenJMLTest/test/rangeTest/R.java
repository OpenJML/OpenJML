public class R {

  void m() {
    //@ ghost var r = 2 ..3 ;
    //@ set var rr = r;
    //@ set var k = r.lo;
    //@ assert k == 2;
    //@ assert r.hi == 3;
    //@ assert (2 .. 3) == (2 .. 3);
  }
}
