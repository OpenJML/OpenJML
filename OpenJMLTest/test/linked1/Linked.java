class W {}

public class Linked {
	//@ model public seq<W> values;
	//@ public represents values = next == null ? seq.<W>of(value) : next.values.prepend(value);
	
	//@ model public \bigint length;
	//@ public represents length = ((next == null) ? (\bigint)1 : 1 + next.length);
	
	//@ model public JMLDataGroup links;
	
	//@ public invariant values.length == length;
	//@ public invariant values[0] == value;
	//@ public invariant next != null ==> values == next.values.prepend(value);
	//@ public invariant next == null ==> values == seq.<W>of(value);
	
	//@ nullable
	public Linked next;//@ in values, length,  links; //@ maps next.values \into values; maps next.length \into length; maps next.links \into links;
	public W value; //@ in values;
	
	//@ ensures this.value == t;
	//@ ensures this.next == null;
	//@ ensures this.values == seq.<W>of(t);
	//@ ensures this.length == 1;
	//@ pure
	public Linked(W t) {
		this.next = next;
		this.value = t;
	}
	
	//@ ensures this.value == t;
	//@ ensures this.next == n;
	//@ ensures this.length == 1 + n.length;
	//@ ensures this.values == n.values.prepend(t);
	//@ pure
	public Linked(W t, Linked n) {
		this.next = n;
		this.value = t;
	}
	
	//@ ensures \result.value == t;
	//@ ensures \result.next == this;
	//@ ensures \result.length == this.length + 1;
	//@ ensures \result.values == this.values.prepend(t);
	//@ pure
	public Linked push(W t) {
		return new Linked(t, this);
	}
	
	//@   requires next == null;
	//@   assignable next, values;
	//@   ensures values == \old(values).add(t);
	//@   ensures value == \old(value);
	//@   ensures next != null && \fresh(next);
	//@ also
	//@   requires next != null;
	//@   assignable links, values;
	//@   ensures next == \old(next) && value == \old(value);
	//@   ensures next.values == \old(next.values).add(t);
	//@   ensures values == next.values.prepend(value);
	public void add(W t) {
		if (next != null) {
			next.add(t);;
		} else {
			next = new Linked(t);
		}
	}
}