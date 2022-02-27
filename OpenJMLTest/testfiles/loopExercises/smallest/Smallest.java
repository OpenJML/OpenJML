public class Smallest {
    // A <=!=> B  means (A) != (B)
    // !(A ==> B && B ==> A)
    //@ requires a.length > 0 <=!=> a.length < Integer.MAX_VALUE;
    //@ requires a.length > 0 <==> a.length > 0;
    //@ requires a.length > 0;
    //@ ensures (\forall int i; 0 <= i && i < a.length; a[\result] <= a[i]);
    static public int smallest(int[] a) {
        int index = 0;
        int smallestIndex = 0;
        while (a.length - index > 0) {
            if (a[index] < a[smallestIndex]) {
                smallestIndex = index;
            }
            index = index + 1;
        }
        return smallestIndex;
    }
}

