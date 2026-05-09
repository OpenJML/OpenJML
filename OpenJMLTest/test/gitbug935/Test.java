public class Test {
    //@  requires arr != null;
    //@  requires \exists int i, j; 0 <= i < j < arr.length; arr[i] == arr[j];
    //@  assigns \nothing;
    //@  ensures \exists int j; \result < j < arr.length; arr[\result] == arr[j];
    //@  ensures \forall int i; 0 <= i < \result; !(\exists int j; i < j < arr.length; arr[i] == arr[j]);
    //@ also
    //@  requires arr != null;
    //@  requires !(\exists int i, j; 0 <= i < j < arr.length; arr[i] == arr[j]);
    //@  assigns \nothing;
    //@  ensures \result == -1;
    public static int firstDuplicate(int[] arr) {
        //@ maintaining 0 <= i <= arr.length - 1 || i == 0;
        //@ maintaining \forall int p; 0 <= p < i; !(\exists int q; p < q < arr.length; arr[p] == arr[q]);
        //@ loop_writes \nothing;
        //@ decreases arr.length - 1 - i;
        for (int i = 0; i < arr.length - 1; i++) {
            //@ maintaining i+1 <= j <= arr.length;
            //@ maintaining \forall int p; 0 <= p < i; !(\exists int q; p < q < arr.length; arr[p] == arr[q]);
            //@ maintaining \forall int p; i+1 <= p < j; arr[i] != arr[p];
            //@ loop_writes \nothing;
            //@ decreases arr.length - j;
            for (int j = i + 1; j < arr.length; j++) {
                if (arr[i] == arr[j]) {
                    return i;
                }
            }
        }
        return -1;
    }
}

