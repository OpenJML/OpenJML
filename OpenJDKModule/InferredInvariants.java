
public class InferredInvariants {
  
  @org.jmlspecs.annotation.Pure
  public InferredInvariants() {
    super();
  }
    /*@
      ensures \forall int i; 0 <= i < a.length; \result >= a[i]; 
      requires a.length > 0; 
   */

  public static int findMax(@org.jmlspecs.annotation.NonNull
  int[] a) {
    int max = a[0];
    //@ loop_invariant 1 <= i <= a.length;
    //@ loop_invariant \forall int k; 0 <= k < i; max >= a[k];
    for (int i = 1; i < a.length; i++) {
      if (a[i] > max) {
        max = a[i];
      }
    }
    /*@ assert \forall int k; 0 <= k < a.length; max >= a[k];*/
    return max;
  }
}