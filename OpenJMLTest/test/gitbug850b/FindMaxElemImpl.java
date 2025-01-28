// This is a modification of gitbug805 in which maxIndex is made a model field, with an appropriate represents clause.
// However, as of this writing, the test fails because super. is illegal syntax in these contexts.
// This test scenario is present as a reminder to add that feature.

public abstract class FindMaxElemImpl extends FindMaxElem
  {
     private /*@ spec_public @*/ int maxIndex; //@ in super.maxIndex;
     //@ represents super.maxIndex = maxIndex;

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
