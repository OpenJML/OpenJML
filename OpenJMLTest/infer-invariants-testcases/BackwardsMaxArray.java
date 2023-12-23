public class BackwardsMaxArray {

    //@ ensures \forall int i; 0 <= i < a.length; \result >= a[i];
    //@ requires a.length > 0;
    public static int findMax(int[] a) {
        int max = a[a.length - 1];
        for (int i = a.length - 1; i >= 0; i--) {
            if (a[i] > max) {
                max = a[i];
            }
        }
        //@ assert \forall int k; -1 < k < a.length; max >= a[k];
        return max;
    }
}


