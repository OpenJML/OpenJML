class ArrayInit {
    //@ requires 0 < arr.length;
    //@ ensures (\forall int k; 0 <= k && k <= arr.length; ((2 * k) + 1) <= arr[k]);
    public void arrayInit() {
        int[] arr;
        int i = 0;
        while (i < arr.length) {
            arr[i] = 2 * i + 1;
            ++i;
        }
    }
}