//@ nullable_by_default
public class RotateMatrix180 {
    //@  requires A == null || A.length == 0 ||
    //@    A[0] == null || A[0].length == 0 ||
    //@    (\exists int i; 1 <= i < A.length; (A[i] == null || A[i].length != A[0].length));
    //@  assigns \nothing;
    //@  ensures \result == null;
    //@ also
    //@  requires !(A == null || A.length == 0 ||
    //@    A[0] == null || A[0].length == 0 ||
    //@    (\exists int i; 1 <= i < A.length; (A[i] == null || A[i].length != A[0].length)));
    //@  assigns \nothing;
    //@  ensures \fresh(\result);
    //@  ensures \result.length == A.length;
    //@  ensures \forall int i; 0 <= i < \result.length; \fresh(\result[i]);
    //@  ensures \forall int i; 0 <= i < \result.length; \result[i].length == A[i].length;
    //@  ensures \forall int i; 0 <= i < A.length; \forall int j; 0 <= j < A[0].length; \result[i][j] == A[A.length - i - 1][A[0].length - j - 1];
    //@ behaviors disjoint;
    //@ behaviors complete;
    public static int[][] rotateMatrix180(int[][] A) {
        if (A == null || A.length == 0) return null;
        if (A[0] == null || A[0].length == 0) return null;
        int m = A.length;
        int n = A[0].length;

        //@ maintaining 1 <= i <= m;
        //@ maintaining \forall int j; 1 <= j < i; A[j] != null && A[j].length == n;
        //@ loop_writes i;
        //@ decreases m - i;
        for (int i = 1; i < m; i++) {
            if (A[i] == null || A[i].length != n) {
                return null;
            }
        }

        int[][] ret = new int[m][n];
        //@ assert \fresh(ret);
        //@ assert \forall int i; 0 <= i < ret.length; \fresh(ret[i]);
        //@ maintaining 0 <= i <= m;
        //@ maintaining \forall int p; 0 <= p < i; \forall int q; 0 <= q < n; ret[p][q] == A[m-1-p][n-1-q];
        //@ loop_writes i, ret[*][*];
        //@ decreases m - i;
        for (int i = 0; i < m; i++) {
            //@ maintaining 0 <= j <= n;
            //@ maintaining \forall int k; 0 <= k < j; ret[i][k] == A[m-1-i][n-1-k];
            //@ loop_writes j, ret[i][*];
            //@ decreases n - j;
            for (int j = 0; j < n; j++) {
                ret[i][j] = A[m-1-i][n-1-j];
            }
        }

        return ret;
    }
}

