public class Loop {
  //@ requires i >= 0;
  public static void m(int i) {
    zasd:
    //@ loop_invariant i >= 0;
    for (;i>0;) {
      i -= 1;
      if (i != 0) continue zasd;
    }
  }
}
