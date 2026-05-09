// This test checks that \pre and \Pre in a callee specifications refer to the 
// precondition of the callee, not of the caller
public class PRE {
  public int k;

  //@ requires 0 <= i <= 1000; requires 0 <= k <= 2000;
  //@ assigns k;
  //@ ensures k == \pre(k) + i;
  public void m(int i) {
    k += i;
  //@ assert k == \old(k, \Pre) + i;
  }

  //@ requires k >= 0;
  //@ assigns k;
  //@ ensures k == \old(k)-1;
  //@ final inline
  public void q() {
    k--;
    //@ assert k == \old(k-1, \Pre);
  }

  //@ requires 0 <= k <= 1000;
  //@ ensures k == 8 + \old(k);
  public void mm() {
    int j = 4;
    k = k + 1;
    j = j +4;
    m(j);
    q();
  }
}
    
