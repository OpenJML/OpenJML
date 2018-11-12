public class Test {

	//@ public normal_behavior
	//@   requires p >= 0;
	//@   ensures (p&1) ==  p%2;
	//@ pure
	public void lemma(int p) {}
	
	//@ requires k >= 0;
	//@ requires k <= Integer.MAX_VALUE/2 && k >= Integer.MIN_VALUE/2;
	public void mbit(int k) {
		k = 2*k;
		boolean b = ((k+1)&1) == 1;
		//@ assert b;
	}

	//@ requires k <= Integer.MAX_VALUE/2 && k >= -1; // The -1 just so the counterexample is always the same
	public void m(int k) {
		//@ show k;
		k = 2*k;
		//@ use lemma((k+1));
		boolean b = ((k+1)&1) == 1; // Error expect4ed when k is -1
		//@ assert b;
	}

	//@ requires k >= 0;
	//@ requires k <= Integer.MAX_VALUE/2 && k >= Integer.MIN_VALUE/2;
	public void mm(int k) {
		//@ show k;
		k = 2*k;
		//@ use lemma((k+1));
		boolean b = ((k+1)&1) == 1;
		//@ assert b;
	}
	
}