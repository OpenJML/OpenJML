package p;
// --compile writes only the Java members: x, a, count(), f() and the constructor
public class H {
    int x;
    int[] a = new int[0];
    static int count() { return 1; }
    //@ ghost int g = count(); // would run count() at construction
    //@ model int m;
    //@ model pure public static int q(); // no body: an invalid class file
    //@ public model boolean allPos() { return (\forall int i; 0 <= i < a.length; a[i] > 0); }
    //@ invariant x >= 0;
    public void f() {
        //@ ghost int k = 0;
        //@ set g = k;
        x++;
    }
    //@ model static class MC {}
}
