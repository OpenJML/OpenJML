

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
    // @ public invariant !links.contains(this);
    
    // @ model public JMLDataGroup links;
        
    //@ nullable
    public Linked<W> next;//@ in size, values, links; // @ maps next.values \into values; maps next.size \into size;
    //@ nullable
    public W value; //@ in values;
    
    //@ public normal_behavior
    //@   ensures \result.value == null;
    //@   ensures \result.next == null;
    //@   ensures \result.values == seq.<T>empty();
    //@   ensures \result.size == 0;
    //@ pure
    public static <T> Linked<T> empty() {
        return new Linked(null, null);
    }
    
    //@ private normal_behavior
    //@   ensures this.value == t;
    //@   ensures this.next == n;
    //@ pure 
    private Linked(/*@ nullable */ W t, /*@ nullable */ Linked n) {
        this.next = n;
        this.value = t;
    }
    
    //@ public normal_behavior
    //@   old \bigint oldsize = this.size;
    //@   old seq<W> oldvalues = this.values;
    //@   old seq<Linked<W>> oldlinks = this.links;
    //@   assignable size, values, links;
    //@   ensures \fresh(this.next);
    //@   ensures this.next.value == t;
    //@   ensures this.next.next == \old(this.next);
    //@   ensures this.size == oldsize + 1;
    //@   ensures this.values.equals(oldvalues.prepend(t));
    //@   ensures this.links.equals(oldlinks.prepend(this.next));
    public void push(W t) {
        //@ assume !links.contains(this);
        Linked v = new Linked(t, next);
        //@ assert !this.links.contains(v);
        this.next = v;
        //@ assert !links.contains(this);
    }
    
    //@ public normal_behavior
    //@   requires next != null;
    //@   old \bigint oldsize = this.size;
    //@   old seq<W> oldvalues = this.values;
    //@   old seq<Linked<W>> oldlinks = this.links;
    //@   assignable size, values, links;
    //@   ensures next == \old(next.next);
    //@   ensures this.size == oldsize - 1;
    //@   ensures this.values.equals(oldvalues.tail(1));
    //@   ensures this.links.equals(oldlinks.tail(1));
    public void pop() {
        //@ assume !links.contains(this);
        this.next = this.next.next;
        //@ assert !links.contains(this);
    }
    
    //@ public normal_behavior
    //@   requires 0 <= n < this.size;
    //@   old \bigint oldsize = this.size;
    //@   old seq<W> oldvalues = this.values;
    //@   assignable size, values, links;
    //@   ensures n == 0 ==> next == \old(next.next);
    //@   ensures n > 0 ==> next == \old(next);
    //@   ensures this.size == oldsize - 1;
    //@   ensures this.values.equals(oldvalues.tail(1));
    public void remove(int n) {
        //@ assert this.next != null;
        if (n == 0) {
            this.next = this.next.next;
        } else {
            //@ halt;
            this.next.remove(n-1);
        }
    }
}