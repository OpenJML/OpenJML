
//@ non_null_by_default immutable
public class Opt2 {
	
	private Opt2(/* nullable */ Object t) {
		value = t;
	}
	

	final public /*@ nullable */ Object value;
	
	//@ public normal_behavior
	//@   ensures \result == (value != null);
	//@ pure heap_free
	public boolean nn() { return value != null; }
}