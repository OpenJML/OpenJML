
//@ immutable
abstract public class escDeterministic {

	//@ ensures true;
	//@ no_state 
	static public int comp(int a) { return 0; }

	public int a;
	public int b;
	public int c;
	
	//@ ensures a == b;
	public void k() {
		a = comp(10);
		b = comp(10);
		//@ assert a == b; // OK 
	}

	//@ ensures a == b;
	public void m() {
		a = comp(10);
		c = 20;
		b = comp(10);
		//@ assert a == b; // OK - a function is independent of heap
	}

	//@ ensures true;
	//@ no_state 
	abstract public int acomp(int a);

	//@ assignable \everything;
	//@ ensures acomp(10) == acomp(10);  // OK
	public void n() {}

}
