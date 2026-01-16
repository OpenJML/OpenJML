public class DivArrayByTwo {
    //@  requires arr == null;
    //@  assigns \nothing;
    //@ also
    //@  requires arr != null;
    //@  assigns arr[*];
    //@  ensures \forall int i; 0 <= i < arr.length; arr[i] == \old(arr[i]) / 2;
    //@ behaviors complete;
    //@ behaviors disjoint;
    public static void DivArrayByTwo(int[] arr) {
        if (arr == null)
            return;

        //@ maintaining 0 <= i <= arr.length;
        //@ maintaining \forall int j; 0 <= j < i; arr[j] == \old(arr[j]) / 2;
        //@ maintaining \forall int k; i <= k < arr.length; arr[k] == \old(arr[k]);
        //@ loop_writes arr[*], i;
        //@ decreases arr.length - i;
        for (int i = 0; i < arr.length; ++i) {
            arr[i] /= 2;
        }
    }
}
