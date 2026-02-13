public class MatrixAdd {
    
    //@ requires a != null && b != null;
    //@ requires a.length >= 2 && b.length >= 2;
    //@ requires \forall int i; 0 <= i < 2; a[i] != null && b[i] != null;
    //@ requires \forall int i; 0 <= i < 2; a[i].length >= 2 && b[i].length >= 2;
    //@ requires \forall int i; 0 <= i < 2; \forall int j; 0 <= j < 2; Integer.MIN_VALUE <= a[i][j] + b[i][j] <= Integer.MAX_VALUE;
    //@ ensures \fresh(\result);
    //@ ensures \result.length == 2 && \forall int i; 0 <= i < 2; \result[i].length == 2;
    //@ ensures \forall int i; 0 <= i < 2; \forall int j; 0 <= j < 2; \result[i][j] == a[i][j] + b[i][j]; 
    public int[][] add(int[][] a, int[][] b) {
        int[][] c = new int[2][2];
        // @ assert \forall int n; 0 <= n < 2; \fresh(c[n]); // FIXME - no trouble proving this
        // @ assert \forall int m; 0 <= m < 2; \forall int n; 0 <= n < 2; a[m][n] == \pre(a[m][n]) && b[m][n] ==  \pre(b[m][n]); // FIXME - no trouble proving this

        //@ maintaining 0 <= i <= 2;
        //@ maintaining \forall int m; 0 <= m < 2; \forall int n; 0 <= n < 2; a[m][n] == \pre(a[m][n]) && b[m][n] == \pre(b[m][n]); // FIXME - not sure why this is needed
        //@ maintaining \forall int m; 0 <= m < i; \forall int n; 0 <= n < 2; c[m][n] == a[m][n] + b[m][n];
        //@ loop_writes i, c[*][*];
        //@ decreases 2 - i;
        for (int i = 0; i < 2; i++) {
            //@ maintaining 0 <= j <= 2;
            //@ maintaining \forall int m; 0 <= m < 2; \forall int n; 0 <= n < 2; a[m][n] == \pre(a[m][n]) && b[m][n] == \pre(b[m][n]); // FIXME - not sure why this is needed
            //@ maintaining \forall int m; 0 <= m < i; \forall int n; 0 <= n < 2; c[m][n] == a[m][n] + b[m][n];
            //@ maintaining \forall int k; 0 <= k < j; c[i][k] == a[i][k] + b[i][k];
            //@ loop_writes j, c[i][*];
            //@ decreases 2 - j;
            for (int j = 0; j < 2; j++) {
                c[i][j] = a[i][j] + b[i][j];
            }
        }
        return c;
    }
}

