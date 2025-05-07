// This solves the original problem by removing the duplicate declaration of maxIndex.
// This variation on gitbug850 fixes the problem by removing the declaration of maxIndex in FindMaxElemImpl
// Then the duplicated specification can also be removed.

public abstract class FindMaxElemImpl extends FindMaxElem
  {
     // private /*@ spec_public @*/ int maxIndex;

     //@ also
     //@ requires 0 < a.length;
     //@ assignable maxIndex;
     //@ ensures 0 <= maxIndex && maxIndex < a.length;
     /*@ ensures (\forall int i; 0 <= i && i < a.length;
                                 a[i] <= a[maxIndex]);   @*/
     public void maxElem(int a[])
     {
          maxIndex = 0;
          int k = 1;
          //@ maintaining 0 <= k && k <= a.length;
          //@ maintaining 0 <= maxIndex && maxIndex < a.length;
          /*@ maintaining (\forall int i; 0 <= i && i < k;
                                          a[i] <= a[maxIndex]); @*/
          while (k < a.length) {
              if (a[maxIndex] < a[k]) {
                  maxIndex = k;
              }
              k = k+1;
          }
     }
  }

abstract class FindMaxElemImpl2 extends FindMaxElem
{
   // private /*@ spec_public @*/ int maxIndex;

   public void maxElem(int a[])
   {
        maxIndex = 0;
        int k = 1;
        //@ maintaining 0 <= k && k <= a.length;
        //@ maintaining 0 <= maxIndex && maxIndex < a.length;
        /*@ maintaining (\forall int i; 0 <= i && i < k;
                                        a[i] <= a[maxIndex]); @*/
        while (k < a.length) {
            if (a[maxIndex] < a[k]) {
                maxIndex = k;
            }
            k = k+1;
        }
   }
}
