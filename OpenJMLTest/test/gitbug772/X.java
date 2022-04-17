public class X {

/*@
  model public static void test(\real j, \real k) {
    //@ assert j >= 0 && k > 0 ==> j%k >= 0;
    // @ assert j >= 0 && k < 0 ==> j%k >= 0;
    // @ assert j < 0 && k > 0 ==> j%k <= 0;
    // @ assert j < 0 && k < 0 ==> j%k <= 0;
    // @ assert k != 0 ==> (j/k)*k + (j%k) == j;
  }
*/
}
