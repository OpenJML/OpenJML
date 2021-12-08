public class Test {
	
	//@  requires i >= 0;
	//@  diverges false;
	//@ also
	//@  requires i < 0;
	//@  diverges true;
	public void m1(int i) {
		if (i < 0) abort();
	}
	
	//@  diverges false;
	public void m2(int i) {
		if (i < 0) abort();
	}
	
	//@  requires i >= 0;
	//@  diverges false;
	//@ also
	//@  requires i < 0;
	//@  diverges true;
	public void m3(int i) {
		if (i <= 0) abort();
	}
	
	//@ ensures false;
	//@ signals_only SecurityException;
	//@ diverges true;
	public void abort() { System.exit(0); }
}