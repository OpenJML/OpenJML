
public class escDeterministic2 {

	//@ ensures true;
	//@ no_state 
	//@ model static public int comp(int a);

	//@ ghost public int a;
	//@ ghost public int b;
	//@ ghost public int c;
	
	//@ ensures a == b;
	public void m() {
		//@ set a = comp(10);
		//@ set c = 20;
		//@ set b = comp(10);
		//@ assert a == b;
	}
	
	//@ ensures comp(10) == comp(10);
	public void n() {}

}
