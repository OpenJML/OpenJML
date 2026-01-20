import java.util.Arrays;
//@ nullable_by_default
public class Test {
    //@  requires a == null;
    //@  assigns \nothing;
    //@  ensures \result == null;
    //@ also
    //@  requires a != null;
    //@  assigns \nothing;
    //@  ensures \fresh(\result);
    //@  ensures \result.length == a.length;
    //@  ensures \forall int i; 0 <= i < a.length; a[i] != null ==> \fresh(\result[i]);
    //@  ensures \forall int i; 0 <= i < \result.length; Arrays.equals(\result[i], a[i]);
    public static int[][] deep_copy(int[][] a) {
        if (a == null) return null;
        int n = a.length;
        int[][] copy = new int[n][];
        //@ maintaining 0 <= i <= n;
        //@ maintaining \forall int j; 0 <= j < i; a[j] != null ==> \fresh(copy[j]);
        //@ maintaining \forall int j; 0 <= j < i; Arrays.equals(copy[j], a[j]);
        //@ loop_writes i, copy[*];
        //@ decreases n - i;
        for (int i = 0; i < n; i++) {
            copy[i] = a[i] != null ? a[i].clone() : null;
        }
        return copy;
    }
}

//@ nullable_by_default
class TestB {
     //@  requires a == null;
     //@  assigns \nothing;
     //@  ensures \result == null;
     //@ also
     //@  requires a != null;
     //@  assigns \nothing;
     //@  ensures \fresh(\result);
     //@  ensures \result.length == a.length;
     //@  ensures \forall int i; 0 <= i < a.length; a[i] != null ==> \fresh(\result[i]);
     //@  ensures \forall int i; 0 <= i < \result.length; Arrays.equals(\result[i], a[i]);
     public static int[][] deep_copy(int[][] a) {
         if (a == null) return null;
         int n = a.length;
         int[][] copy = new int[n][];
         //@ maintaining 0 <= i <= n;
         //@ maintaining \forall int j; 0 <= j < i; a[j] != null ==> \fresh(copy[j]);
         //@ maintaining \forall int j; 0 <= j < i; Arrays.equals(copy[j], a[j]);
         //@ loop_writes i, copy[*];
         //@ decreases n - i;
         for (int i = 0; i < n; i++) {
             if (a[i] == null) copy[i] = null;
             else {
                 copy[i] = new int[a[i].length];
                 //@ maintaining 0 <= j <= copy[i].length;
                 //@ maintaining \forall int k; 0 <= k < j; copy[i][k] == a[i][k];
                 //@ loop_writes j, copy[i][*];
                 //@ decreases copy[i].length - j;
                 for (int j = 0; j < copy[i].length; j++) {
                     copy[i][j] = a[i][j];
                 }
             }
         }
         return copy;
     }
 }
