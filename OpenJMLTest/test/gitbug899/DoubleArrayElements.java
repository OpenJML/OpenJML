public class DoubleArrayElements {
    //@ requires arr != null;
    //@ assigns arr[*];
    //@ ensures (\forall int i; 0 <= i < arr.length; arr[i] == 2 * \old(arr[i]));
    //@ ensures arr == null ==> \nothing;
    //@ behaviors complete;
    //@ behaviors disjoint;
    public static void doubleElements(int[] arr) {
        if (arr == null)
            return;
        //@ maintaining 0 <= i <= arr.length;
        //@ loop_writes arr[*], i;
        //@ decreases arr.length - i;
        for (int i = 0; i < arr.length; ++i) {
            arr[i] = 2 * arr[i];
        }
    }
}
