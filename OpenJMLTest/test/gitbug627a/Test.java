public class Test {
	
	public static void main(String... args) {
		m();
	}
	
	public static void m() {
		
		//@ loop_invariant 10 <= i && i <= 15;
		//@ loop_invariant i == \count + 10;
		for (int i=10; i<15; i++) {
			//@ show \old(i,\LoopInit), \old(i,\LoopBody);
			//@ assert \old(i,\LoopInit) == 10;
			//@ assert \old(i,\LoopBody) == \count + 10;
		}
	}
}