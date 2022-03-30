// openjml --esc $@
/** This file contains a worked (specified and verified) example of a singly-linked list using JML and OpenJML. 
 * It is intended to illustrate techniques that can be used for other simple recursive data structures. 
 * This example uses model methods.
 * 
 * A list of values of type T is an instance of the public class ListMM<T>. The actual links are instances of the non-public
 * nested class Node<T>; both classes inherit from Link<T>, which contains common functionality. The linked-list is formed
 * by the typical chain of 'next' field references, with a null reference at the end of the list. The starting point, the List
 * object, is not a part of the abstract list.
 * 
 */

/** Parent class for ListMM and Node containing the 'next' field and common functionality */
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
    //@   reads next, next.next, next.nextFields, next.value, next.valueFields;
    //@   ensures \result == (next == null ? seq.<T>empty() : next.values().prepend(next.value));
    //@ pure helper
    //@ model public seq<T> values(); // sequence of values after the current Link, not including the current Link
    
    //@ public normal_behavior    
    //@   reads next, next.next, next.nextFields; // FIXME - does not work as nextFields
    //@   ensures \result == ((next == null) ? 0 : 1 + next.size());
    //@   ensures \result >= 0;
    //@ pure helper
    //@ model public \bigint size();
    
    
    
    // @ public normal_behavior
    // @   reads next, nextFields, next.value, next.valueFields;
    // @   ensures \result <==> (\invariant_for(this) && (this.next != null ==> \invariant_for(this.next)));
    // @ pure helper
    // @ model public boolean invariants();

    //@ public model JMLDataGroup nextFields;
    //@ public model JMLDataGroup valueFields;
    
    
    // @ public invariant this.invariants(); // recursive down the list
    //@ public invariant this.owner != null && allMine(this.owner);
    //@ public invariant values().size() == this.size();
    //@ public invariant links.size() == this.size();
    // @ public invariant !links.contains(this);

    //@ nullable spec_public
    protected ListMM.Node<T> next; //@ in valueFields, nextFields, links; 
    //@ maps next.valueFields \into valueFields; maps next.nextFields \into nextFields; maps next.links \into links;
    
    //@ protected normal_behavior
    //@ pure helper
    protected Link() {
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
        if (n == 0) {
            return next.value();
        } else {
            //@ assert next.values() == this.values().tail(1);
            return next.value(n-1);
        }
    }

    /** Removes the nth value from the list */
    //@ public normal_behavior
    //@   requires 0 <= n < this.size();
    //@   old \bigint oldsize = this.size();
    //@   old seq<T> oldvalues = this.values();
    //@   assignable next, nextFields;
    //@   ensures this.size() == oldsize - 1;
    //@   ensures this.values().size == oldvalues.size - 1;
    // @   ensures n==0 ==> this.values() == oldvalues.tail(1); // FIXME
    public void remove(int n) {
        //@ assert this.next != null;
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
            //@ assert this.next.values() == oldvalues.tail(1);
            //@ assert this.next.allMine(this.next.owner);
            //@ assert this.next.next != null ==> this.next.next.values().size == oldvalues.size - 2;
            //@ assert this.next.next != null ==> this.next.next.values() == oldvalues.tail(1).tail(1);
            //@ assert this.next.next != null ==> this.next.next.links.size == oldsize - 2;
            this.next = this.next.next;
            //@ assert newsize == (this.next == null ? 0 : this.next.size() + 1);
            //@ assert this.size() == newsize;
            //@ assert this.next != null ==> this.next.values().size == oldvalues.size - 2;
            //@ assert this.values().size == newsize;//oldvalues.size - 1;
            //@ assert this.next != null ==> this.next.links.size == oldsize - 2;
            //@ assert this.links.size == newsize;//oldsize - 1;
            //@ assert this.values().size == this.size();
            //@ assert this.next != null ==> this.next.allMine(this.next.owner);
            //@ assert allMine(this.owner);
            //@ assert n==0 ==> this.values() == oldvalues.tail(1);
        } else {
            //@ reachable;
            //@   assert \invariant_for(this);
            //@   assert \invariant_for(next);
            //@ reachable;
            //@ ghost \bigint poldsize = this.next.size();
            // @ ghost var poldvalues = this.next.values();
            // @ havoc this.next.next, this.next.nextFields;
            // @ halt;
           this.next.remove(n-1);
            // @ reachable;
            //@   assert this.next.size() == poldsize - 1;
            // @ reachable;
           // @ halt;
            // @   assume \invariant_for(this.next);
            // @ reachable;
            // @   assume \invariant_for(next.next);
            // @ reachable;
            // @   assume this.next.values().size == poldvalues.size - 1;

            // @ reachable;
            // @ assert (next != null) ==> next.invariants();
            // @ assert invariants();
            //@ assert this.size() == newsize;
            //@ assert this.owner != null && allMine(this.owner);
            //@ assert this.next.allMine(this.next.owner);
            //@ assert this.values().size == this.size();
            //@ assert this.links.size == oldsize - 1;
            //@ assert n==0 ==> this.values() == oldvalues.tail(1); 
            // @ halt;
            // @ reachable;
        }
        // @ assert (next != null) ==> next.invariants();
        // @ assert invariants();
        //@ assert this.owner != null && allMine(this.owner);
        //@ assert this.next != null ==> this.next.allMine(this.next.owner);
        //@ assert this.size() == newsize;
        //@ assert this.values().size == this.size();
        //@ assert this.links.size == oldsize - 1;
        // @ halt;
        //@   assert this.size() == oldsize - 1;
        //@   assert this.values().size == oldvalues.size - 1;
        //@   assert n==0 ==> this.values() == oldvalues.tail(1); // FIXME
        // @ halt;
    }
}

public class ListMM<T> extends Link<T> {
    
    //@ public invariant this.owner == this;

    //@ public normal_behavior
    //@   ensures \result.values() == seq.<TT>empty();
    //@   ensures \result.size() == 0;
    //@   ensures \result.links == seq.<Link<TT>>empty();
    //@   ensures \result.next == null;
    //@   ensures \result.owner == \result;
    //@ pure
    public static <TT> ListMM<TT> empty() {
        return new ListMM<TT>();
    }
    
    //@ private normal_behavior
    //@   ensures this.next == null;
    //@   ensures this.owner == this;
    //@ pure
    private ListMM() {
        this.next = null;
        //@ set this.owner = this;
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
    //@   assignable next, nextFields;
    //@   ensures this.size() == oldsize - 1;
    //@   ensures this.values() == oldvalues.tail(1);
    //@   ensures next == \old(next.next);
    public void pop() {
        //@ assert this.owner == this && this.allMine(this.owner);
        //@ assert this.next.owner == this && this.next.allMine(this.owner);
        //@ assert this.next.next != null ==> this.next.next.allMine(this.next.owner);
        //@ assert this.next != null;
        //@ assert this.values().size == this.size();
        //@ assert this.next.values().size == this.next.size();
        //@ assert this.next.next != null ==> this.next.next.values().size == this.next.next.size();
        //@ assert next.links.size() == this.next.size();
        //@ assert this.next.next != null ==> this.next.next.links.size == this.next.next.size();
        //@ ghost seq<T> oldvalues = this.values();
        //@ ghost seq<T> oldnvalues = this.next.values();
        //@ assert oldnvalues == oldvalues.tail(1);
        this.next = this.next.next;
        //@ assert this.size() == (this.next == null ? 0 : this.next.size() + 1);
        //@ assert this.size() == \old(this.size()) - 1;
        //@ assert this.next != null ==> this.next.values().size == this.next.size();
        //@ assert this.next != null ==> this.next.links.size == this.next.size();
        //@ assert this.values() == oldnvalues;
        //@ assert this.values() == oldvalues.tail(1);
        //@ assert this.allMine(this.owner) <==> (this.owner == owner && (this.next != null ==> this.next.allMine(this.owner)));
        //@ assert this.allMine(this.owner);
    }
    
    static class Node<T> extends Link<T> {

        /** Constructs a new link with given value and next field; for internal use only */
        //@ private normal_behavior
        // @   requires next != null ==> \invariant_for(next); // FIXME
        //@   ensures this.next == next;
        //@   ensures this.value == value;
        //@ pure helper
        private Node(T value, /*@ helper nullable */ Node<T> next) {
            this.value = value;
            this.next = next;
        }
        
        //@ spec_public
        private T value; //@ in valueFields; maps next.valueFields \into valueFields;
        
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
    
    /** properties of an empty list */
    public static <Y> void testEmpty(Y y) {
        var in = ListMM.<Y>empty();
        //@ assert in.size() == 0;
        //@ assert in.values().size() == 0;
        //@ assert in.values() == seq.<Y>empty();
    }

    /** pushing a value and then retrieving it */
    public static <Y> void testPushValue(ListMM<Y> in, Y y, Y yy) {
        in.push(y);
        //@ assert in.size() == \old(in.size()) + 1;
        //@ assert in.values() != \old(in.values());
        //@ assert in.value(0) == y;
        in.push(yy);
        //@ assert in.value(1) == y;
        //@ assert in.value(0) == yy;
    }

    /** pushing a value and then retrieving it */
    //@ requires in.size() >= 2;
    public static <Y> void testPopValue(ListMM<Y> in) {
        Y y = in.value(1);
        in.pop();
        Y yy = in.value(0);
        //@ assert y == yy;
    }
    
    /** pushing and popping leaves the list unchanged */
    public static <Y> void testPushPop(ListMM<Y> in, Y y) {
        in.push(y);
        //@ assert in.size() == \old(in.size()) + 1;
        //@ assert in.values() != \old(in.values());
        in.pop();
        //@ assert in.size() == \old(in.size());
        //@ assert in.values() == \old(in.values());
    }
    
    /** pushing and removing the zeroth element leaves the list unchanged */
    public static <Y> void testPushRemove(ListMM<Y> in, Y y) {
        in.push(y);
        //@ assert in.size() == \old(in.size()) + 1;
        //@ assert in.values() != \old(in.values());
        in.remove(0);
        //@ assert in.size() == \old(in.size());
        //@ assert in.values() == \old(in.values());
    }
    
    /** pushing a value on one list does not change the other */
    //@ requires in != other;
    //@ requires in.values() == other.values();
    public static <Y> void testNI1(Y y, ListMM<Y> in, ListMM<Y> other) {
        in.push(y);
        //@ assert in.values().tail(1) == other.values();
    }
    
    /** popping a value from one list does not change the other */
    //@ requires in != other;
    //@ requires in.values() == other.values();
    //@ requires in.size() > 0;
    public static <Y> void testNI2(ListMM<Y> in, ListMM<Y> other) {
        //@ assert in.size() == other.size();
        //@ ghost seq<Y> oldvalues = in.values();
        in.pop();
        //@ assert oldvalues.tail(1) == in.values();
        //@ assert in.values() == other.values().tail(1);
    }
    
    /** removing a value (other than the 0th) from one list might change the other,
     * except when the owner invariant is used */
    //@ requires in != other;
    //@ requires in.values() == other.values();
    //@ requires in.size() > 1;
    public static <Y> void testNI3(ListMM<Y> in, ListMM<Y> other) {
        //@ ghost seq<Y> oldvalues = in.values();
        in.remove(1);
        //@ assert oldvalues.size - 1 == in.size();
        //@ assert other.values().size() - 1 == in.size();   // Should not be provable without the owner invariant
    }
    
    /** two different lists may have the same first element, except when the owner invariant is used */
    //@ requires in != other;
    //@ requires in.size() > 0;
    //@ requires other.size() > 0;
    public static <Y> void testNI4(ListMM<Y> in, ListMM<Y> other) {
        //@ assert in.next.owner == in;
        //@ assert other.next.owner == other;
        //@ assert in.next != other.next;    // Should not be provable without the owner invariant
    }
    
    /** using rep-exposure to change a value still does not change the other list if the owner invariant is used */
    //@ requires in != other;
    //@ requires in.values() == other.values();
    //@ requires in.size() > 1;
    /*@ model public static <Y> void testNI5(ListMM<Y> in, ListMM<Y> other, Y y) {
        ghost \bigint n = in.size();
        assume in.next.value != y;
        assert in.values().size() == other.values().size();
        assert in.size() == other.size();
        assert in.size() == n;
        in.next().value = y;
        assert in.size() == n;
        assert in.size() == other.size();
        assert in.values() != other.values();    // Should not be provable without the owner invariant
        assert in.values().tail(1) == other.values().tail(1);
    }
    @*/
}