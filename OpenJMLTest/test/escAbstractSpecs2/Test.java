public class Test {

	public static class C {
		
		public boolean init = true;
		
		//@ public normal_behavior
		//@   ensures init;
		//@ model public C(); // ERROR - no such constructor
		
		public C(int i) {
			this(); // ERROR - no such constructor
		}
		
	}


}