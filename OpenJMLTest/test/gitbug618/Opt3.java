

public class Opt3 {
	
	private Opt3(/* nullable */ Test t) {  // FIXME - determine if this nullable is in or out
		value = t;
	}
	

	final public /*@ nullable */ Test value;
	
	//@ public normal_behavior
	//@   { return value != null; }
	//@ pure
	public boolean nn() { return value != null; }
}
