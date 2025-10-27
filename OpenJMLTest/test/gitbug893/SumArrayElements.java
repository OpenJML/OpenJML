import java.math.BigInteger;

public class SumArrayElements {

    //@  requires arr != null;
    //@  requires n == -1;
    //@  assigns \nothing;
    //@  ensures \result == 0;
    //@ also
    //@  requires arr != null;
    //@  requires 0 <= n < arr.length;
    //@  assigns \nothing;
    //@  ensures \result == arr[n] + sumFirstNElements(arr, n-1);
    //@ behaviors disjoint;
    //@ model public static pure \bigint sumFirstNElements(int arr[], int n) {
    //@     if (n == -1) {
    //@         return 0;
    //@     }
    //@     return arr[n] + sumFirstNElements(arr, n-1);
    //@ }

    //@ requires arr != null;
    //@ assigns \nothing;
    // @ ensures \fresh(\result);
    //@ ensures \result == sumFirstNElements(arr, arr.length-1);
    public static BigInteger sumArrayElements(int arr[]) {
        BigInteger sum = BigInteger.ZERO;
        //@ maintaining 0 <= i <= arr.length;
        //@ maintaining sum == sumFirstNElements(arr, i-1);
        //@ loop_writes i, sum;
        //@ decreases arr.length - i;
        for (int i = 0; i < arr.length; ++i) {
            sum = sum.add(BigInteger.valueOf(arr[i]));
        }
        return sum;
    }
}
