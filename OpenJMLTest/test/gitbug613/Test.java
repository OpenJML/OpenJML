//@ non_null_by_default
public class Test {
	
	private static int zz;
	//@ private static invariant zz == 1;
	private int aa;
	//@ private invariant aa == 3;
	
	//@ public normal_behavior
	//@   requires i >= 0;
	//@ also public exceptional_behavior
	//@   requires i < 0;
	//@   signals_only RuntimeException;
	public Test(int i) {
		zz = 2;
		if (i < 0) throw new RuntimeException();
		zz = 1;
		aa = 3;
	}
}

 class Test2 {
	
	private static int zz;
	//@ private static invariant zz == 1;
	private int aa;
	//@ private invariant aa == 3;
	
	//@ public normal_behavior
	//@   requires i >= 0;
	//@ also public exceptional_behavior
	//@   requires i < 0;
	//@   signals_only RuntimeException;
	public Test2(int i) {
		zz = 1;
		if (i < 0) throw new RuntimeException();
		aa = 3;
	}
}