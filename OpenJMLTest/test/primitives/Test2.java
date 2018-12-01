
//@ pure immutable nullable_by_default
abstract class testcol<T> implements IJmlPrimitiveType {
	
	//@ axiom (\forall T t;; !testcol.<T>empty().contains(t));
	//@ axiom (\forall testcol<T> c; (\forall T t;; c.add(t).contains(t)));
	//@ axiom (\forall testcol<T> c; (\forall T t, tt; t != tt; c.add(t).contains(tt) == c.contains(tt)));

	//@ model public \bigint size;
	
	//@ public normal_behavior
	//@   ensures \result.size() == 0;
	//@ skipesc
	//@ model public static <S> testcol<S> empty();
		
	//@ public normal_behavior
	//@   ensures \result == size;
	//@ helper function
	//@ model abstract public \bigint size();
	
	//@ public normal_behavior
	//@   ensures \result.size == \old(size) + 1;
	//@ helper function
	abstract public testcol<T> add(T t);
	
	//@ public normal_behavior
	//@ helper function
	abstract public boolean contains(T t);
}

public class Test2<X> {
	
	//@ ensures (testcol.<X>empty().size() == 0);
	public void lemma21() {}
	
	//@ ensures c.add(x).add(xx).contains(x);
	public void lemma22(testcol<X> c, X x, X xx) {}
	
//	public void m(testtype t) {
//		//@ ghost testtype tt = t;
//		//@ assert tt.suc() == t.suc();
//	}
}
