public class MinMaxExample {

    //@ requires 0 < a.length;
    //@ requires (\forall int i; 0 <= i < a.length; 0 < a[i]);
    //@ ensures \result == (\min int m; 0 <= m < a.length; a[m]);
    //@ spec_pure
    public int minOfPosArray (int[] a) {
        int val = a[0];
        int k;
        for (k = 0; k < a.length; k++) {
            //@ assume 0 <= k < a.length;
            if (a[k] < val) {
                val = a[k];
            }
        }
        //@ assume k == a.length;
        //@ assume (\forall int m; 0 <= m < k; val <= a[m]);
        //@ assume (\exists int n; 0 <= n < a.length; val == a[n]);
        return val;
    }

    //@ requires 0 < a.length;
    //@ requires (\forall int i; 0 <= i < a.length; 0 < a[i]);
    //@ ensures \result == (\max int m; 0 <= m < a.length; a[m]);
    //@ spec_pure
    public int maxOfPosArray (int[] a) {
        int val = a[0];
        int k;
        for (k = 0; k < a.length; k++) {
            //@ assume 0 <= k < a.length;
            if (val < a[k]) {
                val = a[k];
            }
        }
        //@ assume k == a.length;
        //@ assume (\forall int m; 0 <= m < k; a[m] <= val);
        //@ assume (\exists int n; 0 <= n < a.length; val == a[n]);
        return val;
    }

}
