public class R {

  public static void main(String ... args) {
    //@ ghost var r = 2 ..3 ;
    //@ set var rr = r;
    //@ set var k = r.lo;
    //@ assert k == 2;
    //@ assert r.hi == 3;
    //@ assert (2 .. 3) == (2 .. 3);
    //@ assert (2 .. 3) != (2 .. 3); // ERROR
  }
}
