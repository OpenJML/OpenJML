public class Test {
    //@ requires arr != null;
    //@ assigns arr[*];
    //@ ensures \forall int i; 0 <= i < arr.length; arr[i] == 2 * \old(arr[i]);
    //@ also
    //@ requires arr == null;
    //@ assigns \nothing;
    //@ ensures \nothing;
    //@ behaviors disjoint;
    //@ behaviors complete;
    public static void doubleElements(int[] arr) {
        if (arr == null)
            return;

        //@ maintaining 0 <= i <= arr.length;
        //@ maintaining \forall int j; 0 <= j < i; arr[j] == 2 * \old(arr[j]);
        //@ loop_writes arr[*], i;
        //@ decreases arr.length - i;
        for (int i = 0; i < arr.length; ++i) {
            arr[i] = 2 * arr[i];
        }
    }
}