

public class escDeterministic {

	//@ ensures \result == comp(a);
	// @ accessible \nothing;
	//@ pure 
	abstract public int comp(int a);

	public int a;
	public int b;
	
	//@ ensures a == b;
	public void m() {
		a = comp(10);
		b = comp(10);
	}

}
