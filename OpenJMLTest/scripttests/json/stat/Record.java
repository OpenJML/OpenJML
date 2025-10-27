public class Record {
    record R(int i, int j) {}
    public void p(Record r) {
      int p = switch (r) { case R(ii,jj) -> 0; default -> 1; };
      
      //@ loop_invariant 0 <= k && k <= 10;
      //@ loop_modifies k;
      //@ loop_decreases 10 - k;
      for (int k=0; k < 10; k++) {}
      while (true) {}
      do {} while (true);
      int[] a = new int[10];
      for (int e: a) {} 
      boolean b = (r instanceof R(int ii,int jj));
  }
}
