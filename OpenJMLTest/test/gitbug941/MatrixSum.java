//@ nullable_by_default
public class MatrixSum {
    //@ // Both matrices are valid and both are N x M. N must be > 0.
    //@ requires a != null && b != null;
    //@ requires a.length > 0;
    //@ requires a.length == b.length;
    //@ requires \forall int i; 0 <= i < a.length; a[i] != null && b[i] != null;
    //@ requires \forall int i; 0 <= i < a.length; a[i].length == b[i].length;
    //@ // Avoid jagged arrays
    //@ requires a.length > 0 ==> \forall int i; 0 <= i < a.length; a[i].length == a[0].length;
    //@ // Matrix sum does not underflow or overflow
    //@ requires \forall int i; 0 <= i < a.length; \forall int j; 0 <= j < a[0].length;
    //@   Integer.MIN_VALUE <= a[i][j] + b[i][j] <= Integer.MAX_VALUE;
    //@ assigns \nothing;
    //@ // Result assertions
    //@ ensures \fresh(\result);
    //@ ensures \forall int i; 0 <= i < \result.length; \fresh(\result[i]); 
    //@ ensures \result.length == a.length;
    //@ ensures \result.length > 0 ==> \result[0].length == a[0].length;
    //@ ensures \forall int i; 0 <= i < \result.length; \result[i].length == a[i].length;
    //@ ensures \forall int i; 0 <= i < a.length; \forall int j; 0 <= j < a[0].length;
    //@   \result[i][j] == a[i][j] + b[i][j];
    public static int[][] matrixSum(int[][] a, int[][] b) {
        int n = a.length;
        int m = a[0].length;

        int[][] c = new int[n][m];

        //@ maintaining 0 <= i <= n;
        //@ maintaining \forall int p; 0 <= p < n; \forall int q; 0 <= q < m; Integer.MIN_VALUE <= a[p][q] + b[p][q] <= Integer.MAX_VALUE;
        //@ maintaining \forall int p; 0 <= p < i; \forall int q; 0 <= q < m; c[p][q] == a[p][q] + b[p][q];
        //@ loop_writes i, c[*][*];
        //@ decreases n - i;
        for (int i = 0; i < n; i++) {
            //@ maintaining 0 <= j <= m;
            //@ maintaining \forall int p; 0 <= p < n; \forall int q; 0 <= q < m; Integer.MIN_VALUE <= a[p][q] + b[p][q] <= Integer.MAX_VALUE;
            //@ maintaining \forall int k; 0 <= k < j; c[i][k] == a[i][k] + b[i][k];
            //@ loop_writes j, c[i][*];
            //@ decreases m - j;
            for (int j = 0; j < m; j++) {
                c[i][j] = a[i][j] + b[i][j];
            }
        }

        return c;
    }
}

