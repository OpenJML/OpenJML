public class APMax implements AProc<Integer> {
    protected /*@ spec_public @*/ Integer maxSeen = Integer.MIN_VALUE;
                                    //@ in objectState; 
    /*@ also
      @   requires 0 <= i && i < a.length;
      @   assignable maxSeen;
      @   ensures maxSeen == Math.max(\old(maxSeen),a[i]); @*/
    public void run(Integer[] a, int i) {
        if (a[i] > maxSeen) {
            maxSeen = a[i];
        }
    }
    //@ ensures \result == maxSeen;
    public /*@ pure @*/ Integer getMax() { return maxSeen; }
}
