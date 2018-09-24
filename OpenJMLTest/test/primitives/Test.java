
//@ pure immutable nullable_by_default
abstract class testtype implements IJmlPrimitiveType {
	
	//@ axiom (\forall testtype t;; t.suc().prev() == t);
	
	static public testtype zero;
	
	//@ skipesc
	private testtype() {}
	
	//@ ensures \result == zero;
	//@ helper function
	abstract public testtype testtype();
	
	//@ ensures \result != this;
	//@ helper function
	abstract public testtype suc();
	
	//@ ensures \result != this;
	//@ helper function
	abstract public testtype prev();
}

public class Test {
	
	//@ ensures t.suc() != t;
	public void lemma1(testtype t) {}
	
	//@ ensures t.suc().prev() == t;
	public void lemma2(testtype t) {}
	
	public void m(testtype t) {
		//@ ghost testtype tt = t;
		//@ assert tt.suc() == t.suc();
	}
}
