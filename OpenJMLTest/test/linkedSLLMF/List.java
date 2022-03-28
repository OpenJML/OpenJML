// openjml --esc $@
/** This file contains a worked (specified and verified) example of a singly-linked list using JML and OpenJML. 
 * It is intended to illustrate techniques that can be used for other simple recursive data structures. 
 * This example uses model fields.
 * 
 * A list of values of type W is an instance of the public class List<W>. The actual links are instances of the non-public
 * nested class Value<W>; both classes inherit from Link<W>, which contains common functionality. The linked-list is formed
 * by the typical chain of 'next' field references, with a null reference at the end of the list. The starting point, the List
 * object, is not a part of the abstract list.
 * 
 * @author davidcok
 *
 */
// Specified with model fields
public class List<W> extends Link<W> {
    
    //@ public invariant this.owner == this;
    
    /** Creates an empty list -- just an anchor node with null 'next' field */
    //@ public normal_behavior
    //@   ensures \result.values == seq.<T>empty();
    //@   ensures \result.size == 0;
    //@   ensures \result.links == seq.<Link<T>>empty();
    //@   ensures \result.next == null;
    //@   ensures \result.owner == \result;
    //@ pure
    public static <T> List<T> empty() {
        return new List<T>();
    }
    
    //@ private normal_behavior
    //@   ensures this.next == null;
    //@   ensures this.owner == this;
    //@ pure
    private List() {
        this.next = null;
        //@ set this.owner = this;
    }
    
    /** Pushes a new value onto the front of the list */
    //@ public normal_behavior
    //@   assignable size, values, links;
    //@   ensures this.size == \old(size) + 1;
    //@   ensures this.values == \old(values).prepend(t);
    //@   ensures this.links == \old(links).prepend(this.next);
    //@ also private normal_behavior
    //@   assignable this.next;
    //@   ensures \fresh(this.next);
    //@   ensures this.next.value == t;
    //@   ensures this.next.next == \old(this.next);
    public void push(W t) {
        //@ assert allMine(this);
        //@ assert this.next != null ==> this.next.allMine(this);
        var v = new List.Value<W>(t, next);
        //@ assert v.next == this.next;
        //@ set v.owner = this;
        //@ assert (v.owner == this && (v.next != null ==> v.next.allMine(v.owner)));
        //@ assert v.allMine(this);
        this.next = v;
        //@ assert this.next != null ==> this.next.allMine(owner);
        //@ assert this.allMine(this);
    }
    
    /** Removes the first value from the list */
    //@ public normal_behavior
    //@   requires next != null;
    //@   assignable size, values, links;
    //@   ensures this.size == \old(size) - 1;
    //@   ensures this.values == \old(values).tail(1);
    //@   ensures this.links == \old(links).tail(1);
    //@   ensures next == \old(next.next);
    public void pop() {
        //@ assert this.owner == this && this.allMine(this.owner);
        //@ assert this.next.owner == this && this.next.allMine(this.owner);
        //@ assert this.next.next != null ==> this.next.next.allMine(this.next.owner);
        //@ ghost \bigint n = next.size;
        //@ ghost seq<W> oldnvalues = this.next.values;
        //@ ghost seq<Link<W>> oldnlinks = this.next.links;
        //@ assert next.size == this.size - 1;
        this.next = this.next.next;
        //@ assert this.size == n;
        //@ assert this.values == oldnvalues;
        //@ assert this.links == oldnlinks;
        //@ assert this.owner != null;
        //@ assert this.allMine(this.owner) <==> (this.owner == owner && (this.next != null ==> this.next.allMine(this.owner)));
        //@ assert this.allMine(this.owner);
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
        
        //@ spec_public
        private W value; //@ in values;
        
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
    //@ ghost helper nullable public List<V> owner; //@ in ownerFields; maps next.ownerFields \into ownerFields;

    //@ model public seq<V> values; // sequence of values after the current Link, not including the current Link
    //@ public represents values = next == null ? seq.<V>empty() : next.values.prepend(next.value);

    //@ model public seq<Link<V>> links;
    //@ public represents links = next == null ? seq.<Link<V>>empty() : next.links.prepend(next);

    // True if my owner is the argument and all nodes after me have the argument as their owners.
    //@ public normal_behavior
    //@   reads this.owner, this.next.ownerFields, this.links;
    //@   ensures \result == (this.owner == owner && (next != null ==> next.allMine(owner)));
    //@ model pure helper public boolean allMine(List<V> owner);

    //@ model public \bigint size; 
    //@ public represents size = ((next == null) ? 0 : 1 + next.size);
    
    //@ public invariant this.owner != null && allMine(this.owner);
    //@ public invariant values.size() == size;
    //@ public invariant links.size() == size;
    //@ public invariant !links.contains(this);

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
    //@   requires 0 <= n < this.size;
    //@   assignable size, values, links;
    //@   ensures this.size == \old(this.size) - 1;
    //@   ensures n == 0 ==> next == \old(next.next);
    //@   ensures n == 0 ==> values == \old(values).tail(1);
    //@   ensures n > 0 ==> next == \old(next);
    public void remove(int n) {
        if (n == 0) {
            //@ assert this.owner != null && allMine(this.owner);
            //@ assert this.next.allMine(this.next.owner);
            //@ assert this.next.next != null ==> this.next.next.allMine(this.next.next.owner);
            //@ assert this.owner == this.next.owner;
            //@ assert this.next.next != null ==> this.next.owner == this.next.next.owner;
            this.next = this.next.next;
            //@ assert this.owner != null;
            //@ assert this.next != null ==> this.next.allMine(this.next.owner);
            //@ assert this.allMine(this.owner) <==> (this.next != null ==> this.next.allMine(this.owner));
            //@ assert this.allMine(this.owner);
        } else {
            this.next.remove(n-1);
            //@ assert this.owner != null && allMine(this.owner);
        }
        xyzxyz: {}
        //@ assert this.owner == \old(this.owner);
        //@ assert this.owner != null && allMine(this.owner);
    }
}

class Test {
    
    /** properties of an empty list */
    public static <Y> void testEmpty(Y y) {
        var in = List.<Y>empty();
        //@ assert in.size == 0;
        //@ assert in.values.size() == 0;
        //@ assert in.values == seq.<Y>empty();
    }

    /** pushing a value and then retrieving it */
    public static <Y> void testPushValue(List<Y> in, Y y, Y yy) {
        in.push(y);
        //@ assert in.size == \old(in.size) + 1;
        //@ assert in.values != \old(in.values);
        //@ assert in.value(0) == y;
        //@ halt;
        in.push(yy);
        //@ assert in.value(1) == y;
        //@ assert in.value(0) == yy;
    }
    
    /** pushing a value and then retrieving it */
    //@ requires in.size >= 2;
    public static <Y> void testPopValue(List<Y> in) {
        Y y = in.value(1);
        //@ reachable;
        in.pop();
        //@ reachable;
        Y yy = in.value(0);
        //@ reachable;
        //@ assert y == yy;
    }
    
    /** pushing and popping leaves the list unchanged */
    public static <Y> void testPushPop(List<Y> in, Y y) {
        in.push(y);
        //@ assert in.size == \old(in.size) + 1;
        //@ assert in.values != \old(in.values);
        in.pop();
        //@ assert in.size == \old(in.size);
        //@ assert in.values == \old(in.values);
    }
    
    /** pushing and removing the zeroth element leaves the list unchanged */
    public static <Y> void testPushRemove(List<Y> in, Y y) {
        in.push(y);
        //@ assert in.size == \old(in.size) + 1;
        //@ assert in.values != \old(in.values);
        in.remove(0);
        //@ assert in.size == \old(in.size);
        //@ assert in.values == \old(in.values);
    }
    
    /** pushing a value on one list does not change the other */
    //@ requires in != other;
    //@ requires in.values == other.values;
    public static <Y> void testNI1(Y y, List<Y> in, List<Y> other) {
        in.push(y);
        //@ assert in.values.tail(1) == other.values;
    }
    
    /** popping a value from one list does not change the other */
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 0;
    public static <Y> void testNI2(List<Y> in, List<Y> other) {
        // @ assume in.size == other.size;
        //@ ghost seq<Y> oldvalues = in.values;
        in.pop();
        //@ assert oldvalues.tail(1) == in.values;
        //@ assert in.values == other.values.tail(1);
    }
    
    /** removing a value (other than the 0th) from one list might change the other,
     * except when the owner invariant is used */
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 1;
    public static <Y> void testNI3(List<Y> in, List<Y> other) {
        //@ ghost seq<Y> oldvalues = in.values;
        in.remove(1);
        //@ assert oldvalues.size - 1 == in.size;
        //@ assert other.values.size - 1 == in.size;   // Should not be provable without the owner invariant
    }
    
    /** two different lists may have the same first element, except when the owner invariant is used */
    //@ requires in != other;
    //@ requires in.size > 0;
    //@ requires other.size > 0;
    public static <Y> void testNI4(List<Y> in, List<Y> other) {
        //@ assert in.next.owner == in;
        //@ assert other.next.owner == other;
        //@ assert in.next != other.next;    // Should not be provable without the owner invariant
    }
    
    /** using rep-exposure to change a value still does not change the other list if the owner invariant is used */
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 1;
    /*@ model public static <Y> void testNI5(List<Y> in, List<Y> other, Y y) {
        ghost \bigint n = in.size;
        assume in.next.value != y;
        assert in.values.size() == other.values.size();
        assert in.size == other.size;
        assert in.size == n;
        in.next().value = y;
        assert in.size == n;
        assert in.size == other.size;
        assert in.values != other.values;    // Should not be provable without the owner invariant
        assert in.values.tail(1) == other.values.tail(1);
    }
    @*/
}
