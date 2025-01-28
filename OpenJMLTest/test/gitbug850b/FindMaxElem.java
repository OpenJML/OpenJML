public abstract class FindMaxElem
  {
     public int maxIndex;

     //@ requires 0 < a.length;
     // @ assignable maxIndex;
     // @ ensures 0 <= maxIndex && maxIndex < a.length;
     /* @ ensures (\forall int i; 0 <= i && i < a.length;
                                 a[i] <= a[maxIndex]);   @*/
     abstract public void maxElem(int a[]);
  }
