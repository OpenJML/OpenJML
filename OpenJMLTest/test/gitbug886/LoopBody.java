public class LoopBody {
  public static void main(String ... args) {
    //+RAC@ set System.out.println("START");
    LoopInit.m();
    int i = 100;
    //@ loop_invariant 0 <= i <= 10;
    //@ loop_invariant i == \count;
    for (i = 0; i < 10; i++) {
      //@ assert \old(i, \LoopBody) == i;
      i++;
      //@ assert \old(i, \LoopBody) + 1 == i;
      for (int j = 0; j < 5; j++) {
        //@ assert \old(i,\LoopBody) == i;
      }
      //@ assert \old(i, \LoopBody) + 1 == i;
      i--;
      //@ assert \old(i,\LoopBody) == i;
      //@ assert i == \count;
    }
    //+RAC@ set System.out.println("END");
  }
}
class LoopInit {

  public static void m() {
    int k = 10;
    for (int i = 0; i<10; i++) {
      k = 11;
      //@ assert \old(k,\LoopInit) == 10;
      //@ loop_writes j, k;
      for (int j = 0; j < 10; j++) {
        k = 12;
        //@ assert \old(k,\LoopInit) == 11;
      }
      //@ assert \old(k,\LoopInit) == 10;
    }
  }
}
   
