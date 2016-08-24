public class ArrOps<T> {
    /*@ extract @*/
    public void forEach(T[] a, AProc<T> p) {
        //@ maintaining 0 <= i && i <= a.length;
        //@ decreasing a.length - i;
        for (int i = 0; i < a.length; i++) {
            p.run(a, i);
        }
    }
}
