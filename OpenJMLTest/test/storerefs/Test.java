public class Test {
	
	//@ model public \datagroup d;
	
	public int[] a = new int[10];
	public boolean b; //@ in d;
	public static boolean bb;
	
	//@ requires a.length > 5;
	//@ assignable b, bb, this.b, Test.bb, Test.*, this.*, this.bb, this.d, a[1], a[2..3], a[*], a[1..*], a[2..3];
	public void m() {
		
	}
}
