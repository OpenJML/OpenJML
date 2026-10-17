public class S implements I {
    private final int[] a = new int[10]; //@ in g; //@ maps a[*] \into g;
    //@ private invariant a.length == 10;

    public void set(int n) { a[n] = 1; }
}
