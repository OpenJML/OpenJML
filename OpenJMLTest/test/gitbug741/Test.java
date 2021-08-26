public class Test {
	
	//@ non_null_by_default
	static public class A {
		
		public void mma(int /*@ non_null @*/[] x) {}
		public void mmb(int /*@ nullable @*/[] x) {}
		public void mmc(int                 [] x) {}
		
		public void mm1() {
			mma(null); // ERROR
		}
		
		public void mm2() {
			mmb(null); // OK
		}
		
		public void mm3() {
			mmc(null); // ERROR
		}
		
	}
	//@ nullable_by_default
	static public class B {
		
		public void nna(int /*@ non_null @*/[] x) {}
		public void nnb(int /*@ nullable @*/[] x) {}
		public void nnc(int                 [] x) {}
		
		public void nn1() {
			nna(null); // ERROR
		}
		
		public void nn2() {
			nnb(null); // OK
			nnc(null); // OK
		}
		
	}
}