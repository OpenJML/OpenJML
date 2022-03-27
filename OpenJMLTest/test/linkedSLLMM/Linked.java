
// A singly-linked list with the first element being a 'head' and not part of the list
// Specified with model methods
public class Linked<W> {
    
    //@ public normal_behavior
    //@   ensures \result.value == null;
    //@   ensures \result.next == null;
    //@   ensures \result.values() == seq.<W>empty();
    //@   ensures \result.size() == 0;
    //@ pure
    public static <W> Linked<W> empty() {
        return new Linked<W>(null, null);
    }
    
    //@ private normal_behavior
    //@   requires n != null ==> n.values().size() == n.size(); // FIXME - should have been assumed
    //@   ensures this.value == t;
    //@   ensures this.next == n;
    //@ pure helper
    private Linked(/*@ nullable */ W t, /*@ nullable */ Linked<W> n) {
        this.next = n;
        this.value = t;
    }
    
    //@ public normal_behavior
    //@   old \bigint oldsize = this.size();
    //@   old seq<W> oldvalues = this.values();
    //@   assignable next;
    //@   ensures \fresh(this.next);
    //@   ensures this.next.value == t;
    //@   ensures this.next.next == \old(this.next);
    //@   ensures this.size() == oldsize + 1;
    //@   ensures this.values()== oldvalues.prepend(t);
    public void push(W t) {
        //@ ghost var oldvalues = this.values();
        //@ ghost \bigint nn = (this.next == null ? -1 : this.next.size());
        Linked<W> v = new Linked<W>(t, next);
        //@ assert nn == (this.next == null ? -1 : this.next.size());
        //@ assert oldvalues == this.values();
        //@ assert v.values() == oldvalues;
        this.next = v;
        //@ assert v.size() == \old(this.size()); // FIXME - this is needed as a lemma
        //@ assert this.values() == oldvalues.prepend(t);
    }
    
    //@ public normal_behavior
    //@   requires this != this.next;
    //@   requires next != null;
    //@   old \bigint oldsize = this.size();
    //@   old seq<W> oldvalues = this.values();
    //@   assignable next; // size, values;
    //@   ensures next == \old(next.next);
    //@   ensures this.size() == \old(this.size()) - 1;
    //@   ensures this.values() == oldvalues.tail(1);
    public void pop() {
        //@ assert this.values().size == this.size();
        //@ assert this.next.values().size == this.next.size();
        //@ ghost seq<W> oldvalues = this.values();
        //@ ghost seq<W> oldnvalues = this.next.values();
        //@ assert oldnvalues == oldvalues.tail(1);
        this.next = this.next.next;
        //@ assert this.size() == (this.next == null ? 0 : this.next.size() + 1);
        //@ assert this.size() == \old(this.size()) - 1;
        //@ assert this.values() == oldnvalues;
        //@ assert this.values() == oldvalues.tail(1);
        //@ assume this.values().size == this.size(); // FIXME - ASSUMED
    }
    
    static class Value<W> extends Link<W> {

        /** Constructs a new link with given value and next field; for internal use only */
        //@ private normal_behavior
        //@   requires next != null ==> \invariant_for(next);
        //@   ensures this.next == next;
        //@   ensures this.value == value;
        //@ pure helper
        private Value(W value, /*@ nullable */ Value<W> next) {
            this.value = value;
            this.next = next;
        }
        
        //@ nullable
        public W value; //@ in valueFields; maps next.valueFields \into valueFields;
        
        /** Returns the value from this link */
        //@ public normal_behavior
        //@   reads value;
        //@   ensures \result == value;
        //@ pure
        public W value() {
            return value;
        }
    }
}

class Link<V> {

    //@ public model JMLDataGroup ownerFields;
    //@ ghost nullable public List<V> owner; //@ in ownerFields; maps next.ownerFields \into ownerFields;


    //@ model public seq<Link<V>> links;
    //@ public represents links = next == null ? seq.<Link<V>>empty() : next.links.prepend(next);

    // True if my owner is the argument and all nodes after me have the argument as their owners.
    //@ public normal_behavior
    //@   reads this.owner, this.next.ownerFields, this.links;
    //@   ensures \result == (this.owner == owner && (next != null ==> next.allMine(owner)));
    //@ model pure helper public boolean allMine(List<V> owner);



    
    
    //@ public normal_behavior
    //@   reads next, next.nextFields, value, next.valueFields;
    //@   ensures \result == (next == null ? seq.<W>empty() : next.values().prepend(next.value));
    //@ pure helper
    //@ model public seq<W> values(); // sequence of values after the current Link, not including the current Link
    
    //@ public normal_behavior    
    //@   reads next, next.nextFields; // FIXME - does not work as nextFields
    //@   ensures \result == ((next == null) ? 0 : 1 + next.size());
    //@   ensures \result >= 0;
    //@ pure helper
    //@ model public \bigint size();

    //@ public invariant values().size == size();
    
    //@ public model JMLDataGroup nextFields;
    //@ public model JMLDataGroup valueFields;
    
    
    
    //@ public invariant values.size() == size;
    //@ public invariant links.size() == size;
    //@ public invariant !links.contains(this);
    //@ public invariant this.owner != null && allMine(this.owner);

    //@ nullable spec_public
    protected List.Value<V> next; //@ in size, values, links; 
    //@ maps next.values \into values; maps next.size \into size; maps next.links \into links;
    
    //@ protected normal_behavior
    //@ pure helper
    protected Link() {
    }

    //@ public normal_behavior // only for demonstration purposes -- exposes representation
    //@   reads next;
    //@   ensures \result == next;
    //@ pure helper
    //@ public model List.Value<V> next();
        
    /** Returns the nth value in the list */
    //@ public normal_behavior
    //@   requires 0 <= n < this.size;
    //@   reads values, links;
    //@   ensures \result == values[n];
    //@ pure
    public V value(int n) {
        if (n == 0) return next.value();
        else return next.value(n-1);
    }

    /** Removes the nth value from the list */
    //@ public normal_behavior
    //@   requires 0 <= n < this.size();
    //@   old \bigint oldsize = this.size();
    //@   old seq<W> oldvalues = this.values();
    //@   assignable next, nextFields;
    //@   ensures this.size() == oldsize - 1;
    //@   ensures this.values().size == oldvalues.size - 1;
    //@   ensures n==0 ==> this.values() == oldvalues.tail(1); // FIXME
    public void remove(int n) {
        //@ ghost \bigint nnn = (this.next.next == null ? 0 : this.next.next.size() + 1);
        //@ ghost \bigint nn = this.next.size();
        //@ ghost seq<W> oldvalues = this.values();
        //@ assert this.values().size == oldvalues.size;
        if (n == 0) {
            this.next = this.next.next;
            //@ assert nn == (this.next == null ? 0 : this.next.size() + 1);
            //@ assert this.size() == nn;
            //@ assert this.values().size == oldvalues.size - 1;
        } else {
            this.next.remove(n-1);
            //@ assert this.size() == nn;
        }
        //@ assert this.size() == nn;
        //@ assume this.values().size == this.size(); // FIXME - ASSUMED
    }
}



class Test {
    
    public static <Y> void test1(Linked<Y> in, Y y) {
        in.push(y);
        //@ assert in.size() == \old(in.size()) + 1;
        //@ assert in.values() != \old(in.values());
        in.pop();
        //@ assert in.size() == \old(in.size());
        //@ assert in.values() == \old(in.values());
    }
    
    public static <Y> void test1a(Linked<Y> in, Y y) {
        //@ ghost var oldsize = in.size();
        //@ ghost var oldvalues = in.values();
        in.push(y);
        //@ assert in.size() == oldsize + 1;
        //@ assert in.values() != oldvalues;
        in.pop();
        //@ assert in.size() == oldsize;
        //@ assert in.values() == oldvalues;
    }
    
    public static <Y> void test2(Y y) {
        var in = Linked.<Y>empty();
        //@ assert in.size() == 0;
        //@ assert in.values().size() == 0;
    }

    public static <Y> void test3(Linked<Y> in, Y y) {
        in.push(y);
        //@ assert in.size() == \old(in.size()) + 1;
        //@ assert in.values() != \old(in.values());
        in.remove(0);
        //@ assert in.size() == \old(in.size());
        //@ assert in.values() == \old(in.values());
    }
    
    public static <Y> void test3a(Linked<Y> in, Y y) {
        //@ ghost var oldsize = in.size();
        //@ ghost var oldvalues = in.values();
        in.push(y);
        //@ assert in.size() == oldsize + 1;
        //@ assert in.values() != oldvalues;
        in.remove(0);
        //@ assert in.size() == oldsize;
        //@ assert in.values() == oldvalues;
    }
    

}