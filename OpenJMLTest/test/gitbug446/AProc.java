public interface AProc<T> {
    /*@ public normal_behavior
      @   requires 0 <= i && i < a.length;
      @   assignable objectState, a[i];   @*/
    void run(T[] a, int i);
}
