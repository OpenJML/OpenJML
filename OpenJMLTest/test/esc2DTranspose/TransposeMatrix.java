     
    public class TransposeMatrix
    {
        //@ requires matrix.length > 0;
        //@ requires matrix[0].length > 0;
       //@ requires (\forall int k; 0 <= k && k < matrix.length; matrix[k] != null);
       //@ requires (\forall int k; 0 <= k && k < matrix.length; matrix[0].length == matrix[k].length);
       //@ ensures (\forall int i, j; i >= 0 && j >= 0 && i < matrix.length && j < matrix[0].length; matrix[i][j] == \result[j][i]);
       //@ ensures matrix.length == \result[0].length;
       //@ ensures matrix[0].length == \result.length;	
       public int[][] transposeMat1(int[][] matrix)
       {
          int m, n, p, q;

          m = matrix.length;
          n = matrix[0].length;
     
          int[][] transpose = new int[n][m];
          //@ assume \forall int i; 0 <= i < n; transpose[i] != null && transpose[i].length == m;
          //@ assume \forall int e; 0<=e<n; \forall int k; 0 <= k < n; (e != k ==> transpose[e] != transpose[k]);
          //@ assume \forall int e; 0<=e<n; (\forall int k; 0 <= k < m; transpose[e] != matrix[k]);

          //@ maintaining 0 <= c && c <= n;
          //@ maintaining \forall int i; 0<=i<c; (\forall int j; 0 <= j < m ; transpose[i][j] == matrix[j][i]);
          //@ decreases n - c;
          for (int c = 0; c < n; c++){
              //@ maintaining 0 <= d && d <= m;
              //@ maintaining (\forall int j; 0 <= j && j < d; transpose[c][j] == matrix[j][c]);
              //@ decreases m - d;
              for (int d = 0; d < m; d++) {
                  transpose[c][d] = matrix[d][c];
              }
          }
          return transpose;
       }
       
       //@ requires matrix.length > 0;
       //@ requires (\forall int k; 0 <= k && k < matrix.length; matrix[k] != null);
       //@ requires (\forall int k; 0 <= k && k < matrix.length; matrix[0].length == matrix[k].length);
       //@ ensures matrix.length == \result[0].length;
       //@ ensures matrix[0].length == \result.length;  
       public int[][] transposeMat2(int[][] matrix)
       {
          int m, n;

          m = matrix.length;
          n = matrix[0].length;
          //@ assume n > 0;
          //@ assume m > 0;
     
          int[][] transpose = new int[n][m];
          //@ assume n > 0 ==> transpose[0] != null;
          //@ assume n > 0 ==> transpose[0].length == n;
          //@ assume \forall int i; 0 <= i < n; transpose[i] != null && transpose[i].length == m;
          //@ assume \forall int e; 0<=e<n; \forall int k; 0 <= k < n; (e != k ==> transpose[e] != transpose[k]);

              //@ maintaining 0 <= d && d <= n;
              //@ decreases n - d;
              for (int d = 0; d < n; d++) {
                  //@ maintaining 0 <= c && c <= m;
                  //@ decreases m - c;
                  for (int c = 0; c < m; c++){
                  // @ assert transpose.length == n; 
                  // @ assert 0 <= d < n;
                  transpose[d][c] = 42;  
              }
          }
          return transpose;
       }

       // @ requires matrix.length > 0;
       // @ requires (\forall int k; 0 <= k && k < matrix.length; matrix[k] != null);
       // @ requires (\forall int k; 0 <= k && k < matrix.length; matrix[0].length == matrix[k].length);
       // @ ensures matrix.length == \result[0].length;
       // @ ensures matrix[0].length == \result.length;  
       public int[][] transposeMat3(int n, int m)
       {
//          int m, n;

          //@ assume n >= 0;
          //@ assume m >= 0;
          int[][] transpose = new int[n][m];

          //@ maintaining 0 <= c && c <= m;
          //@ maintaining \forall int i; 0<=i<n; transpose[i] != null && transpose[i].length == m;
          //@ loop_modifies transpose[*][*];
          //@ decreases m - c;
          for (int c = 0; c < m; c++){
              //@ maintaining 0 <= d && d <= n;
              //@ maintaining \forall int i; 0<=i<n; transpose[i] != null && transpose[i].length == m;
              //@ loop_modifies transpose[*][*];
              //@ decreases n - d;
              for (int d = 0; d < n; d++) {
                  transpose[d][c] = 42;  
              }
          }
          //@ assert n > 0 ==> m == transpose[0].length;
          //@ assert n == transpose.length;  

          return transpose;
       }

    }
