// This solves the original problem by making the super class maxIndex a model field.
// It has to be renamed because we currently cannot write 'in super.maxIndex' or 'represents super.maxIndex = maxIndex'
// The problem of the super. syntax is addressed in gitbug850b

public abstract class FindMaxElemImpl extends FindMaxElem
  {
     private /*@ spec_public @*/ int maxIndex; //@ in maxIndexq;
     //@ represents maxIndexq = maxIndex;

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
