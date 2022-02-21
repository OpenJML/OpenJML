public class OLD {

  public boolean k;

  //@ requires k;
  public void m() {

    //@ assert k; // k is this.k, a boolean

    int k = 0;
    //@ assert k >= 0; // k is the local k, an int
    //@ assert \old(k); // k is this.k, a boolean
  }
  
  //@ requires k == 0;
  public void m1(int k) {
	  a:;
	  k = 1;
	  b:;
	  //@ assert \old(k) == 0;
	  //@ assert k == 1;
	  //@ assert \old(k,a) == 0;
	  //@ assert \old(k,b) == 1;
	  //@ assert \old(k,Here) == 1;
	  //@ assert \old(k,\Here) == 1;
	  //@ assert \old(k,\Old) == 0;
	  //@ assert \old(k,Old) == 0;
	  //@ assert \old(k,\Pre) == 0;
	  //@ assert \old(k,Pre) == 0;
	  //@ assert \pre(k) == 0;
	 
  }
  
  //@ requires k == 0;
  //@ ensures k == 0 && \old(k) == 0;
  public void m2(int k) {
	  Here:;
	  k = 1;
	  Old:;
	  k = 2;
	  Pre:;
	  k = 3;
	  //@ assert \old(k) == 0;
	  //@ assert k == 3;
	  //@ assert \old(k,Here) == 0;
	  //@ assert \old(k,\Here) == 3;
	  //@ assert \old(k,\Old) == 0;
	  //@ assert \old(k,Old) == 1;
	  //@ assert \old(k,\Pre) == 0;
	  //@ assert \old(k,Pre) == 2;
	  //@ assert \pre(k) == 0;
  }
  
  //@ requires k == 0;
  public void m3(int k) {
	  k = 1;
	  //@ refining
	  //@  assignable k;
	  //@  ensures k == 4 && \old(k) == 1;
	  { k = 2; 
	  
	  //@ refining
	  //@  assignable k;
	  //@  ensures k == 3 && \old(k) == 2 && \pre(k) == 0;
	  { k = 3; }
	  
	  k = 4;
	  
	  }
	  //@ refining
	  //@  assignable k;
	  //@  ensures k == 5 && \old(k) == 4 && \pre(k) == 0;
	  { k = 5; }
	  
	  
  }
}
