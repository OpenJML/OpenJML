public class MaxArray {

    //@ ensures \forall int i; 0 <= i < a.length; \result >= a[i];
    //@ requires a.length > 0;
    public static int findMax(int[] a) {
        int max = a[0];
        for (int i = 1; i < a.length; i++) {
            if (a[i] > max) {
                max = a[i];
            }
        }
        //@ assert \forall int i; 0 <= i < a.length; max >= a[i];
        return max;
    }
}

