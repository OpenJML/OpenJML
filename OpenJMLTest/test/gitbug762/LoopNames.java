public class LoopNames {
  public int j;

  public void m() {
    //@ loop_invariant 0 <= i <= 10;
    //@ maintaining 0 <= i <= 10;
    //@ maintains 0 <= i <= 10;
    //@ loop_decreases 10-i;
    //@ decreasing 10-i;
    //@ decreases 10-i;
    //@ loop_writes j;
    //@ loop_assigns j;
    //@ loop_assignable j;
    //@ loop_modifies j;
    for (int i = 0; i < 10; i++) { j = 0; }

  }
}
