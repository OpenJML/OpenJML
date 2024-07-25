

//@ non_null_by_default immutable
public final class Opt1 {
	
	private Opt1(/* nullable */ Object t) {
		value = t;
	}
	
	//@ spec_public
	final private /*@ nullable */Object value;
	
	//@ public normal_behavior
	//@   { return value != null; }
	//@ spec_pure
	public boolean nn() { return value != null; }
}
