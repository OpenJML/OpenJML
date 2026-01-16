public class Test {
    //@ requires a.length == 5;
    //@ requires \forall int i; 0<=i<a.length; a[i].length == a.length;
    public void m(int[][] a) {
        //@ maintains \forall int k; 0 <= k < i; a[k][k] == k;
        //@ maintains 0 <= i <= a.length;
        //@ loop_writes a[*][*];
        for (int i=0; i < a.length; i++) {
            a[i][i] = i;
            //@ assert a[0] == \old(a[0]);
        }
        //@ assert \forall int k; 0 <= k < a.length; a[k][k] == k ;
    }
}