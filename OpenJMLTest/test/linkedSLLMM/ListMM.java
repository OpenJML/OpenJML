
// A singly-linked list with the first element being a 'head' and not part of the list
// Specified with model methods
/** A parent class with common functionality and the 'next' field */
class Link<T> {

    //@ public model JMLDataGroup ownerFields;
    //@ ghost helper nullable public ListMM<T> owner; //@ in ownerFields; maps next.ownerFields \into ownerFields;


    //@ model public seq<Link<T>> links;
    //@ public represents links = next == null ? seq.<Link<T>>empty() : next.links.prepend(next);

    // True if my owner is the argument and all nodes after me have the argument as their owners.
    //@ public normal_behavior
    //@   reads this.owner, this.next.ownerFields, this.links;
    //@   ensures \result == (this.owner == owner && (next != null ==> next.allMine(owner)));
    //@ model pure helper public boolean allMine(ListMM<T> owner);

    //@ public normal_behavior
    //@   reads next, next.nextFields, next.value, next.valueFields;
    //@   ensures \result == (next == null ? seq.<T>empty() : next.values().prepend(next.value));
    //@ pure helper
    //@ model public seq<T> values(); // sequence of values after the current Link, not including the current Link
    
    //@ public normal_behavior    
    //@   reads next, next.nextFields; // FIXME - does not work as nextFields
    //@   ensures \result == ((next == null) ? 0 : 1 + next.size());
    //@   ensures \result >= 0;
    //@ pure helper
    //@ model public \bigint size();

    //@ public invariant values().size == size();
    
    //@ public model JMLDataGroup nextFields;
    //@ public model JMLDataGroup valueFields;
    
    
    
    //@ public invariant values().size() == this.size();
    //@ public invariant links.size() == this.size();
    //@ public invariant !links.contains(this);
    //@ public invariant this.owner != null && allMine(this.owner);

    //@ nullable spec_public
    protected ListMM.Node<T> next; //@ in valueFields, nextFields, links; 
    //@ maps next.valueFields \into valueFields; maps next.nextFields \into nextFields; maps next.links \into links;
    
    //@ protected normal_behavior
    //@   ensures this.next == null;
    //@ pure helper
    protected Link() {
        this.next = null;
    }

    //@ public normal_behavior // only for demonstration purposes -- exposes representation
    //@   reads next;
    //@   ensures \result == next;
    //@ pure helper
    //@ public model ListMM.Node<T> next();
        
    /** Returns the nth value in the list */
    //@ public normal_behavior
    //@   requires 0 <= n < this.size();
    //@   reads valueFields, links;
    //@   ensures \result == values()[n];
    //@ pure
    public T value(int n) {
        if (n == 0) return next.value();
        else return next.value(n-1);
    }

    /** Removes the nth value from the list */
    //@ public normal_behavior
    //@   requires 0 <= n < this.size();
    //@   old \bigint oldsize = this.size();
    //@   old seq<T> oldvalues = this.values();
    //@   assignable next, nextFields;
    //@   ensures this.size() == oldsize - 1;
    //@   ensures this.values().size == oldvalues.size - 1;
    //@   ensures n==0 ==> this.values() == oldvalues.tail(1); // FIXME
    public void remove(int n) {
        //@ ghost \bigint oldsize = this.size();
        //@ ghost \bigint newsize = this.next.size();
        //@ assert newsize == oldsize - 1;
        //@ ghost \bigint nnn = (this.next.next == null ? 0 : this.next.next.size() + 1);
        //@ ghost seq<T> oldvalues = this.values();
        //@ assert this.values().size == oldvalues.size;
        //@ assert this.owner != null && allMine(this.owner);
        //@ assert this.next.allMine(this.next.owner);
        //@ assert this.next.next != null ==> this.next.next.allMine(this.next.next.owner);
        if (n == 0) {
            //@ ghost seq<T> newvalues = this.next.values();
            //@ assert newvalues == oldvalues.tail(1);
            //@ assert this.owner != null && allMine(this.owner);
            //@ assert this.next.allMine(this.next.owner);
            //@ assert this.next.next != null ==> this.next.next.values() == oldvalues.tail(1).tail(1);
            this.next = this.next.next;
            //@ assert newsize == (this.next == null ? 0 : this.next.size() + 1);
            //@ assert this.size() == newsize;
            //@ assume this.values().size == oldvalues.size - 1;  // FIXME
            //@ assert this.values().size == this.size();
            //@ assert this.next != null ==> this.next.allMine(this.next.owner);
            //@ assert this.owner != null && allMine(this.owner);
            // @ assert n==0 ==> this.values() == oldvalues.tail(1); // FIXME
        } else {
            this.next.remove(n-1);
            //@ assert this.size() == newsize;
            //@ assert this.owner != null && allMine(this.owner);
            //@ assert this.next.allMine(this.next.owner);
            //@ assert this.values().size == this.size();
        }
        //@ assert this.owner != null && allMine(this.owner);
        //@ assert this.next != null ==> this.next.allMine(this.next.owner);
        //@ assert this.size() == newsize;
        //@ assert this.values().size == this.size();
        // @ halt;
        //@   assert this.size() == oldsize - 1;
        //@   assert this.values().size == oldvalues.size - 1;
        //@   assume n==0 ==> this.values() == oldvalues.tail(1); // FIXME
        // @ halt;
    }
}

public class ListMM<T> extends Link<T> {
    
    //@ public invariant this.owner == this;

    //@ public normal_behavior
    //@   ensures \result.next == null;
    //@   ensures \result.values() == seq.<TT>empty();
    //@   ensures \result.size() == 0;
    //@ pure
    public static <TT> ListMM<TT> empty() {
        return new ListMM<TT>();
    }
    
    //@ private normal_behavior
    //@   ensures this.next == null;
    //@ pure helper
    private ListMM() {
        this.next = null;
    }
    
    //@ public normal_behavior
    //@   old \bigint oldsize = this.size();
    //@   old seq<T> oldvalues = this.values();
    //@   assignable next;
    //@   ensures \fresh(this.next);
    //@   ensures this.next.value == t;
    //@   ensures this.next.next == \old(this.next);
    //@   ensures this.size() == oldsize + 1;
    //@   ensures this.values()== oldvalues.prepend(t);
    public void push(T t) {
        //@ ghost var oldvalues = this.values();
        //@ ghost \bigint nn = (this.next == null ? -1 : this.next.size());
        //@ assert allMine(this);
        //@ assert this.next != null ==> this.next.allMine(this);
        Node<T> v = new Node<T>(t, next);
        // @ assert nn == (this.next == null ? -1 : this.next.size());
        //@ assert oldvalues == this.values();
        //@ assert v.values() == oldvalues;
        //@ assert v.size() == this.size();
        //@ assert v.size() == \old(this.size());
        // @ assert v.next == this.next;
        //@ set v.owner = this;
        // @ assert nn == (this.next == null ? -1 : this.next.size());
        //@ assert oldvalues == this.values();
        //@ assert v.values() == oldvalues;
        //@ assert v.size() == this.size();
        //@ assert v.size() == \old(this.size());
        //@ assert (v.owner == this && (v.next != null ==> v.next.allMine(v.owner)));
        //@ assert v.allMine(this);
       this.next = v;
       //@ assert v.size() == \old(this.size()); // FIXME - this is needed as a lemma
       //@ assert v.values() == oldvalues; // FIXME - needed as a lemma
       //@ assert this.values() == oldvalues.prepend(t);
       //@ assert this.next != null ==> this.next.allMine(owner);
       //@ assert this.allMine(this);
    }
    
    //@ public normal_behavior
    //@   requires this.size() > 0;
    //@   old \bigint oldsize = this.size();
    //@   old seq<T> oldvalues = this.values();
    //@   assignable next; // size, valueFields;
    //@   ensures next == \old(next.next);
    //@   ensures this.size() == \old(this.size()) - 1;
    //@   ensures this.values() == oldvalues.tail(1);
    public void pop() {
        //@ assert this.owner == this && this.allMine(this.owner);
        //@ assert this.next.owner == this && this.next.allMine(this.owner);
        //@ assert this.next.next != null ==> this.next.next.allMine(this.next.owner);
        //@ assert this.next != null;
        //@ assert this.values().size == this.size();
        //@ assert this.next.values().size == this.next.size();
        //@ ghost seq<T> oldvalues = this.values();
        //@ ghost seq<T> oldnvalues = this.next.values();
        //@ assert oldnvalues == oldvalues.tail(1);
        this.next = this.next.next;
        //@ assert this.size() == (this.next == null ? 0 : this.next.size() + 1);
        //@ assert this.size() == \old(this.size()) - 1;
        // @ assert this.values() == oldnvalues;
        // @ assert this.values() == oldvalues.tail(1);
        //@ assert this.allMine(this.owner) <==> (this.owner == owner && (this.next != null ==> this.next.allMine(this.owner)));
        //@ assert this.allMine(this.owner);
        //@ halt; // FIXME - pop OK to here, not next line
        // @ assume this.values().size == this.size(); // FIXME - ASSUMED
    }
    
    static class Node<T> extends Link<T> {

        /** Constructs a new link with given value and next field; for internal use only */
        //@ private normal_behavior
        // @   requires next != null ==> \invariant_for(next); // FIXME
        //@   ensures this.next == next;
        //@   ensures this.value == value;
        //@ pure helper
        private Node(T value, /*@ nullable */ Node<T> next) {
            this.value = value;
            this.next = next;
        }
        
        public T value; //@ in valueFields; maps next.valueFields \into valueFields;
        
        /** Returns the value from this link */
        //@ public normal_behavior
        //@   reads value;
        //@   ensures \result == value;
        //@ pure
        public T value() {
            return value;
        }
    }
}



class Test {
    
    public static <Y> void test1(ListMM<Y> in, Y y) {
        in.push(y);
        //@ assert in.size() == \old(in.size()) + 1;
        //@ assert in.values() != \old(in.values());
        in.pop();
        //@ assert in.size() == \old(in.size());
        //@ assert in.values() == \old(in.values());
    }
    
    public static <Y> void test1a(ListMM<Y> in, Y y) {
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
        var in = ListMM.<Y>empty();
        //@ assert in.size() == 0;
        //@ assert in.values().size() == 0;
    }

    public static <Y> void test3(ListMM<Y> in, Y y) {
        in.push(y);
        //@ assert in.size() == \old(in.size()) + 1;
        //@ assert in.values() != \old(in.values());
        in.remove(0);
        //@ assert in.size() == \old(in.size());
        //@ assert in.values() == \old(in.values());
    }
    
    public static <Y> void test3a(ListMM<Y> in, Y y) {
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