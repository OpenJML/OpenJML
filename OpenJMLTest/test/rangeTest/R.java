public class R {

  void m() {
    //@ ghost range r = 2 ..3 ;
    //@ ghost var rr = r;
    //@ ghost var k = r.lo;
    //@ assert k == 2;
    //@ assert r.hi == 3;
  }
}
