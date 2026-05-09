// Before the bug fix, this test ran out of memory processing the empty embedded line comment
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
    }
}
