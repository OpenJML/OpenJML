// This tests while and do-while loops, but not sure it adds anything to other tests

public class A {
  
  public void m() {
    int j = 0;
    //@ loop_invariant 0 <= j && j <= 10;
    //@ loop_decreases 10 - j;
    while (j < 10) {
      j++;
    }
    int i = 0;
    //@ loop_invariant 0 <= i && i <= 10;
    //@ loop_decreases 10 - i;
    do {
      i++;
    } while (i < 10);
    i = 0;
    //@ loop_invariant 0 <= i && i <= 10;
    //@ loop_decreases 10 - i;
    do i++; while (i < 10);
    i = 0;
    //@ loop_invariant 0 <= i && i <= 10;
    //@ loop_decreases 10 - i;
    while (i < 10) {
      i++;
    }
  }

  public void n() {
      int j = 0;
      //@ loop_invariant 0 <= j && j <= 10;
      //@ loop_decreases 10 - j;
      while (j < 10) {
        j++;
      }
      int i = 0;
      //@ loop_invariant 0 <= i && i <= 10;
      //@ loop_decreases 10 - i;
      do {
        i++;
      } while (i < 10);
      //@ loop_invariant 0 <= i && i <= 10;
      //@ loop_decreases 10 - i;
      do i++; while (i < 10);
      //@ loop_invariant 0 <= i && i <= 10;
      //@ loop_decreases 10 - i;
      while (i < 10) {
        i++;
      }
    }
}