public class Test {
	
	//@ invariant
	
	//@ true;
	
	public int f;
	
	//@ requires true
    // comment
//@    || false;
public void m() {}

//@ requires true
public
//@    || false;
 void m() {}

	
}