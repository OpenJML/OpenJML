public class T_whileloop {

    //@ ensures \forall int i; 0 <= i < a.length; \result >= a[i];
    //@ requires a.length > 0;
    public static int findMax(int[] a) {
      int max = a[0];
      int i = 1;
      while (i < a.length) {
        if (a[i] > max) {
          max = a[i];
        }
        i++;
      }
      //@ assert \forall int k; 0 <= k < a.length; max >= a[k];
      return max;
  }
}
