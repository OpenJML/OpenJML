public class OddArray {

    //@ requires n >= 0;
    //@ requires n * 2 <= Integer.MAX_VALUE;
    //@ ensures (\forall int i; 0 <= i && i < \result.length; \result[i] % 2 != 0);
    public static int[] makeOddArray(int n) {
        int[] arr = new int[n];

        for (int i = 0; i < n; i++) {
            arr[i] = 2 * i + 1;
        }
        //@ assert (\forall int i; 0 <= i && i < arr.length; arr[i] % 2 != 0);
        return arr;
    }
}

