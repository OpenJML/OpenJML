class W {}

public class Linked {
	
	//@ public invariant values().length == length();
	//@ public invariant values()[0] == value;
	//@ public invariant next != null ==> values().sub(1,values().length) == next.values();
	//@ public invariant next == null ==> values() == seq.<W>of(value);
	
	//@ ensures \result == (next == null ? seq.<W>of(value) : next.values().prepend(value));
	//@ model pure helper public seq<W> values();
	
	//@ ensures \result == ((next == null) ? 1 : 1 + next.length());
	//@ model pure helper public int length();
	
	//@ nullable
	public Linked next;
	public W value;
	
	//@ ensures this.length() == 1;
	//@ ensures this.values() == seq.<W>of(t);
	//@ ensures next == null;
	//@ ensures value == t;
	//@ pure
	public Linked(W t) {
		this.next = null;
		this.value = t;
	}
	
	//@ ensures this.next == n;
	//@ ensures this.value == t;
	//@ ensures this.length() == 1 + next.length();
	//@ ensures this.values() == next.values().prepend(t);
	//@ pure
	public Linked(W t, Linked n) {
		//@ assume n.values().length == n.length();
		//@ ghost seq<W> v = n.values();
		//@ ghost \bigint g = n.values().length;
		//@ ghost \bigint h = n.length();
		//@ assume this != n;
		this.next = n;
		//@ assert n == \old(n);
		//@ assert n.next == \old(n.next);
		//@ assert h == n.length();

		//@ assert g == v.length;
		//@ assert v == n.values();
		//@ assert g == h;
		//@ assert g == n.values().length;
		//@ assume n.values().length == n.length();
		this.value = t;
		//@ assume n.values().length == n.length();
	}
	
	//@ ensures \result.value == t;
	//@ ensures \result.next == this;
	//@ ensures \result.length() == this.length() + 1;
	//@ ensures \result.values() == this.values().prepend(t);
	//@ pure
	public Linked push(W t) {
		return new Linked(t, this);
	}
	
	//@ axiom \forall seq<W> s, ss;; s == ss <==> (s.length == ss.length && \forall int i; 0<=i<s.length; s[i] == ss[i]);
	
	//@ ensures seq.<W>empty().add(t) == seq.<W>of(t);
	//@ pure
	public void lemma1(W t) {}
	
	//@ ensures seq.<W>of(t) == seq.<W>of(t);
	//@ pure
	public void lemma2(W t) {}
}