

// A singly-linked list with the first element being a 'head' and not part of the list
// Specified with model fields
public class Linked<W> {
    //@ model public seq<W> values; // sequence of values after the current Link, not including the current Link
    //@ public represents values = next == null ? seq.<W>empty() : next.values.prepend(next.value);
    //@ model public seq<Linked<W>> links;
    //@ public represents links = next == null ? seq.<Linked<W>>empty() : next.links.prepend(next);
    
    //@ model public \bigint size;
    //@ public represents size = ((next == null) ? (\bigint)0 : 1 + next.size);
    //@ public invariant values.size() == size;
    //@ public invariant links.size() == size;
    //@ public invariant !links.contains(this);
    
    //@ nullable
    public Linked<W> next;//@ in size, values, links; //@ maps next.values \into values; maps next.size \into size; maps next.links \into links;
    //@ nullable
    public W value; //@ in values;
    
    //@ public normal_behavior
    //@   ensures \result.value == null;
    //@   ensures \result.next == null;
    //@   ensures \result.values == seq.<T>empty();
    //@   ensures \result.size == 0;
    //@ pure
    public static <T> Linked<T> empty() {
        return new Linked<T>(null, null);
    }
    
    //@ private normal_behavior
    //@   ensures this.value == t;
    //@   ensures this.next == n;
    //@ pure 
    private Linked(/*@ nullable */ W t, /*@ nullable */ Linked<W> n) {
        this.next = n;
        this.value = t;
    }
    
    //@ public normal_behavior
    //@   assignable this.size, values, links;
    //@   ensures \fresh(this.next);
    //@   ensures this.next.value == t;
    //@   ensures this.next.next == \old(this.next);
    //@   ensures this.size == \old(size) + 1;
    //@   ensures this.values.equals(\old(values).prepend(t));
    //@   ensures this.links.equals(\old(links).prepend(this.next));
    public void push(W t) {
        Linked<W> v = new Linked<W>(t, next);
        this.next = v;
    }
    
    //@ public normal_behavior
    //@   requires next != null;
    //@   assignable size, values, links;
    //@   ensures next == \old(next.next);
    //@   ensures this.size == \old(size) - 1;
    //@   ensures this.values.equals(\old(values).tail(1));
    //@   ensures this.links.equals(\old(links).tail(1));
    public void pop() {
        this.next = this.next.next;
    }
    
    //@ public normal_behavior
    //@   requires 0 <= n < this.size;
    //@   assignable size, values, links;
    //@   ensures n == 0 ==> next == \old(next.next);
    //@   ensures n > 0 ==> next == \old(next);
    //@   ensures this.size == \old(this.size) - 1;
    //@   ensures this.values.equals(\old(values).tail(1));
    // @org.jmlspecs.annotation.Options("--check-feasibility=none")  // FIXME - sometime works, sometimes times out
    public void remove(int n) {
        if (n == 0) {
            this.next = this.next.next;
        } else {
            this.next.remove(n-1);
        }
    }
}