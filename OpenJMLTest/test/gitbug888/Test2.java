public class Test2
{
    //@ public normal_behavior
    //@  requires arr != null;
    //@  requires -1 <= N < arr.length;
    //@  assigns \nothing;
    //@  ensures \result == (N == -1 ? 0 : arr[N] + _sumFirstNElements(arr, N-1));
    //@  measured_by N+1;
    //@ pure
    //@ model public int _sumFirstNElements(int[] arr, int N) {
    //@     if (N == -1) {
    //@         return 0;
    //@     }
    //@     //@ assume Integer.MIN_VALUE <= arr[N] + _sumFirstNElements(arr, N-1) <= Integer.MAX_VALUE;
    //@     return arr[N] + _sumFirstNElements(arr, N-1);
    //@ }

    //@ requires arr != null;
    //@ requires arr.length > 0;
    //@ assigns \nothing;
    //@ ensures \result == _sumFirstNElements(arr, arr.length-1);
    public int sumArray(int[] arr) {
        int sum = 0;
        //@ maintaining 0 <= i <= arr.length;
        //@ maintaining sum == _sumFirstNElements(arr, i-1);
        //@ loop_writes sum;
        //@ decreases arr.length - i;
        for (int i = 0; i < arr.length; ++i) {
            //@ assume Integer.MIN_VALUE <= sum + arr[i] <= Integer.MAX_VALUE;
            sum += arr[i];
        }
        return sum;
    }
}
