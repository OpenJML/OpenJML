public class Test{    
    /*@
      // Two disjoint exhaustive behaviors:
      // 1) If arr is null, the method does nothing.
      // 2) If arr is non-null, every element is replaced by twice its old value.
      //
      // These behaviors are disjoint (arr == null vs arr != null) and cover all cases.
      @
      @   requires arr == null;
      @   assigns \nothing;
      @   ensures arr == null;
      @ also
      @   requires arr != null;
      @   assigns arr[*];
      @   ensures \forall int i; 0 <= i && i < arr.length; arr[i] == 2 * \old(arr[i]);
      @*/
    public static void doubleElements(int[] arr) {
        if (arr == null)
            return;

        //@ maintaining arr != null;
        //@ maintaining 0 <= i && i <= arr.length;
        //@ maintaining \forall int j; 0 <= j && j < i; arr[j] == 2 * \old(arr[j]);
        //@ maintaining \forall int k; i <= k && k < arr.length; arr[k] == \old(arr[k]);
        //@ loop_writes arr[*], i;
        //@ decreases arr.length - i;
        for (int i = 0; i < arr.length; ++i) {
            arr[i] = 2 * arr[i];
        }
    }
}
