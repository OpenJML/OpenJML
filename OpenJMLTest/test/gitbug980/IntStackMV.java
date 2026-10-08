public interface IntStackMV {
    static final int MAX_SIZE = 10000;

    //@ public model instance \seq<Integer> elems;

    //@ public model instance int size;

    //@ public instance invariant 0 <= size <= MAX_SIZE;

    //@ requires 0 <= n < size;
    //@ reads size, elems[n];
    //@ spec_pure
    public int nthElement(int n);

    //@ requires 0 <= n < size;
    //@ reads size, elems, elems[n];
    //@ spec_pure
    public int nthElement2(int n);

    /*@ requires 0 <= n < size;
      @ assignable elems[n];
      @*/
    public void set(int n, int i);
}
