public class Test {

	//@ public normal_behavior
	//@   requires p >= 0;
	//@   ensures (p&1) ==  p%2;
	//@ pure
	public void lemma(int p) {}
	
	//@ requires k <= Integer.MAX_VALUE/2 && k >= Integer.MIN_VALUE/2;
	public void m(int k) {
		k = 2*k;
		//@ use lemma((k+1));
		//@ assert ((k+1)&1) == 1;
	}

	//@ requires k >= 0;
	//@ requires k <= Integer.MAX_VALUE/2 && k >= Integer.MIN_VALUE/2;
	public void mm(int k) {
		//@ show k;
		k = 2*k;
		//@ use lemma((k+1));
		//@ assert ((k+1)&1) == 1;
	}
}