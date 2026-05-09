public class Test {

  public void m(int k) {
    //@ ghost var z1 = \old(k,\LoopInit); // ERROR
    //@ ghost var z2 = \old(k,\LoopBody); // ERROR
    for (int i=0; i<10; i++) {}
    //@ ghost var z3 = \old(k,\LoopInit); // ERROR
    //@ ghost var z4 = \old(k,\LoopBody); // ERROR
    for (int i=0; i<10; i++) {
        for (int j = 0; j<10; j++) {
        }
        //@ ghost var z5 = \old(i,\LoopBody); // OK
        //@ ghost var z6 = \old(j,\LoopBody); // ERROR
    }
  }
}
