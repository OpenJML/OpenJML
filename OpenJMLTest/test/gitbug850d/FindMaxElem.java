public abstract class FindMaxElem
  {
     //@ model public int maxIndexq;

     //@ requires 0 < a.length;
     //@ assignable maxIndexq;
     //@ ensures 0 <= maxIndexq && maxIndexq < a.length;
     /*@ ensures (\forall int i; 0 <= i && i < a.length;
                                 a[i] <= a[maxIndexq]);   @*/
     abstract public void maxElem(int a[]);
  }
