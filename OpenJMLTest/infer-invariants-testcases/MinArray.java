public class MinArray {

    //@ ensures \forall int i; 0 <= i < a.length; \result <= a[i];
    //@ requires a.length > 0;
    public static int findMin(int[] a) {
        int min = a[0];
        for (int i = 1; i < a.length; i++) {
            if (a[i] < min) {
                min = a[i];
            }
        }
        //@ assert \forall int i; 0 <= i < a.length; min <= a[i];
        return min;
    }
}

