public class FirstEven {

    //@ ensures (\result == -1) || (a[\result] % 2 == 0);
    public static int findFirstEven(int[] a) {
        int i = 0;
        while (i < a.length && a[i] % 2 != 0) {
            i++;
        }
        if (i == a.length) {
            return -1;
        }
        //@ assert a[i] % 2 == 0;
        return i;
    }
}

