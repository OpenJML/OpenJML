public class Test {
    
    //@ requires m >= 0 && n>= 0;  // FIXME - fails to prove if m is allowed to be 0
    //@ ensures \fresh(\result);
    //@ ensures \result.length == m;
    //@ ensures \forall int i; 0<=i<m; \result[i] != null && \result[i].length == n;
    //@ ensures \forall int e; 0<=e<m; \forall int k; 0 <= k < n; \result[e][k] == e+k;
    public static int[][] m(int m, int n) {
        
        int[][] a = new int[m][n];
        //@ assert a != null;
        //@ assert a.length == m;
        //@ assert m > 0 ==> a[0] != null;  // FIXME - proof fails if the following are not assumed
        //@ assert m > 0 ==> a[0].length == n;
        //@ assert \forall int i; 0 <= i < m; a[i] != null && a[i].length == n;
        //@ assert \forall int e; 0<=e<m; \forall int k; 0 <= k < m; (e != k ==> a[e] != a[k]);
        x: ;
        
        //@ loop_invariant 0 <= i <= m;
        //@ loop_invariant \forall int k; 0<=k<m; a[k] != null && a[k].length == n;
        //@ loop_invariant \forall int e; 0<=e<i; \forall int k; 0 <= k < n; a[e][k] == e+k;
        //@ loop_modifies a[*][*];
        //@ loop_decreases m-i;
        for (int i=0; i<m; i++) {
            //@ loop_invariant 0 <= j <= n;
            //@ loop_invariant \forall int k; 0<=k<m; a[k] != null && a[k].length == n;
            //@ loop_invariant \forall int e; 0<=e<i; \forall int k; 0 <= k < n; a[e][k] == e+k;
            //@ loop_invariant \forall int k; 0 <= k < j; a[i][k] == i+k;
            //@ loop_modifies a[*][*];
            //@ loop_decreases n-j;
            for (int j=0; j<n; j++) {
                a[i][j] = i+j;
            }
            //@ assert \forall int k; 0 <= k < n; a[i][k] == i+k;
        }
        //@ assert \forall int e; 0<=e<m; \forall int k; 0 <= k < n; a[e][k] == e+k;
        return a;
    }
}