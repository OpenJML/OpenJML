public class Loops {

  public void m1() {
    int i = 10;
    //@ loop_invariant i == \old(i,\LoopInit) + \count;
    //@ loop_assigns i;
    for (i = 1; i < 5; i++) {
      i += 20;
      //@ check \old(i,\LoopInit) == 1;
      //@ check \old(i, \LoopBody) == \old(i,\LoopInit) + \count;
      i -= 20;
    }
  }

  public void m2() {
    //@ loop_invariant i == \count;
    for (int i = 0; i < 5; i++) {
      i += 20;
      //@ check \old(i,\LoopInit) == 0;
      //@ check \old(i, \LoopBody) == \count;
      i -= 20;
    }
  }

  public void m3() {
    int i = 2;
    //@ loop_invariant i == \old(i,\LoopInit) + \count;
    //@ loop_writes i;
    while (i<5) {
      i += 20;
      //@ check \old(i,\LoopInit) == 2;
      //@ show \old(i, \LoopBody), \count;
      //@ check \old(i, \LoopBody) == \old(i,\LoopInit) + \count;
      i -= 20;
      //@ show i, \count;
      //@ check i == \old(i,\LoopInit) + \count;
      i++;
    }
  }

  public void m4() {
    int i = 0;
    //@ loop_invariant i == \count;
    //@ loop_assigns i;
    do {
      i += 20;
      //@ check \old(i,\LoopInit) == 0;
      //@ check \old(i, \LoopBody) == \count;
      i -= 20;
      i++;
    } while (i<5);
  }

  public void m5(int[] a) {
    int j = 123;
    //@ loop_assigns j,k;
    for (int k: a) {
      //@ check k == a[\count];
      //@ check k == \old(k, \LoopBody);
      k += 0;
      j = 0;
      //@ check \old(k, \LoopBody) == a[\count];
      //@ check \old(j, \LoopInit) == 123;
    }
  }
}
