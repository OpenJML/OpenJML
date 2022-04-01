// ## openjml --esc --progress --timeout=300 List.java
/** This file contains a worked (specified and verified) example of a singly-linked list using JML and OpenJML. 
 * It is intended to illustrate techniques that can be used for other simple recursive data structures. 
 * This example uses model fields.
 * 
 * A list of values of type T is an instance of the public class List<T>. The actual links are instances of the non-public
 * nested class Node<T>; both classes inherit from Link<T>, which contains common functionality. The linked-list is formed
 * by the typical chain of 'next' field references, with a null reference at the end of the list. The starting point, the List
 * object, is not a part of the abstract list.
 * 
 */

/** Parent class for List and Node containing the 'next' field and common functionality */
class Link<T> {

    //@ public model JMLDataGroup ownerFields;
    //@ ghost helper nullable public List<T> owner; //@ in ownerFields; maps next.ownerFields \into ownerFields;

    //@ model public seq<T> values; // sequence of values after the current Link, not including the current Link
    //@ public represents values = next == null ? seq.<T>empty() : next.values.prepend(next.value);

    //@ model public seq<Link<T>> links;
    //@ public represents links = next == null ? seq.<Link<T>>empty() : next.links.prepend(next);

    // True if my owner is the argument and all nodes after me have the argument as their owners.
    //@ public normal_behavior
    //@   reads this.owner, this.next.ownerFields, this.links;
    //@   ensures \result == (this.owner == owner && (next != null ==> next.allMine(owner)));
    //@ model pure helper public boolean allMine(List<T> owner);

    //@ model public \bigint size; 
    //@ public represents size = ((next == null) ? 0 : 1 + next.size);
    
    //@ public invariant this.owner != null && allMine(this.owner);
    //@ public invariant values.size() == size;
    //@ public invariant links.size() == size;
    //@ public invariant !links.contains(this);

    //@ nullable spec_public
    protected List.Node<T> next; //@ in size, values, links, ownerFields; 
    //@ maps next.values \into values; maps next.next \into values; maps next.next.values \into values;
    //@ maps next.size \into size; maps next.next \into size; maps next.next.size \into size;
    //@ maps next.links \into links; maps next.next \into links; maps next.next.links \into links;
    
    //@ protected normal_behavior
    //@ pure helper
    protected Link() {
    }

    /** Returns the nth value in the list */
    //@ public normal_behavior
    //@   requires 0 <= n < this.values.size;
    //@   reads values, links;
    //@   ensures \result == values[n];
    //@ pure
    public T value(int n) {
        if (n == 0) {
            return next.value();
        } else {
            return next.value(n-1);
        }
    }

    /** Removes the nth value from the list */
    //@ public normal_behavior
    //@   requires 0 <= n < this.size;
    //@   assignable size, values, links, ownerFields, next.size;
    //@   ensures this.size == \old(this.size) - 1;
    //@   ensures this.values.size() == \old(this.values.size()) - 1;
    //@   ensures this.links.size() == \old(this.links.size()) - 1;
    //@   ensures n == 0 ==> values == \old(values).tail(1);
    //@   ensures n == 0 ==> links == \old(links).tail(1);
    //@   ensures n == 0 ==> next == \old(next.next);
    //@   ensures n > 0 ==> next == \old(next);
    public void remove(int n) {
        if (n == 0) {
            //@ ghost \bigint oldsize = this.size;
            //@ assert this.next.size == oldsize - 1;
            //@ assert this.next.next != null ==> this.next.next.size == oldsize - 2;
            //@ assert allMine(this.owner);
            //@ assert this.next.allMine(this.next.owner);
            //@ assert this.next.next != null ==> this.next.next.allMine(this.next.next.owner);
            //@ assert this.owner == this.next.owner;
            //@ assert this.next.next != null ==> this.next.owner == this.next.next.owner;
            //@ assert this.next.values == this.values.tail(1);
            //@ assert this.next.next != null ==> this.next.next.values == this.next.values.tail(1);
            //@ ghost nullable Link<T> nxx = this.next.next;
            //@ assert nxx != null ==> nxx.allMine(nxx.owner);
            //@ assert nxx != null && nxx.next != null ==> nxx.links == nxx.next.links.prepend(nxx.next);
            //@ assert nxx != null && nxx.next != null ==> this.links.contains(nxx.next);
            // !this.links.contains(this) is an invariant. Combined with the above, it implies the following.
            //@ assert nxx != null ==> (Object)this != nxx.next; // So that we know this.next.next.allMine is not affected by the change to this.next.
            this.next = this.next.next;
            //@ assert this.next != null ==> this.next.size == oldsize - 2;
            //@ assert this.size == oldsize - 1;
            //@ assert this.next != null ==> this.next.allMine(this.next.owner);
            //@ assert this.next != null ==> this.next.values == this.values.tail(1);
            //@ assert this.values == \old(this.values).tail(1);
            //@ assert this.values.size() == \old(this.values.size()-1);
            //@ assert this.links == \old(this.links).tail(1);
            //@ assert this.links.size() == \old(this.links.size()-1);
        } else {
            this.next.remove(n-1);
            //@ reachable;
            //@ assert this.next.size == \old(this.next.size) - 1;
            //@ assert this.values.size() == \old(this.values.size()-1);
            //@ assert this.links.size() == \old(this.links.size()-1);
            //@ assert allMine(this.owner);
            //@ assert this.size == \old(this.size) - 1;
        }
        //@ assert allMine(this.owner);
    }
}

public class List<T> extends Link<T> {
    
    //@ public invariant this.owner == this;
    
    /** Creates an empty list -- just an anchor node with null 'next' field */
    //@ public normal_behavior
    //@   ensures \result.values == seq.<TT>empty();
    //@   ensures \result.size == 0;
    //@   ensures \result.links == seq.<Link<TT>>empty();
    //@   ensures \result.next == null;
    //@   ensures \result.owner == \result;
    //@ pure
    public static <TT> List<TT> empty() {
        return new List<TT>();
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
    //@   assignable size, values, links, ownerFields;
    //@   ensures this.size == \old(size) + 1;
    //@   ensures this.values == \old(values).prepend(t);
    //@   ensures this.links == \old(links).prepend(this.next);
    //@ also private normal_behavior
    //@   assignable size, values, links, ownerFields;
    //@   ensures \fresh(this.next);
    //@   ensures this.next.value == t;
    //@   ensures this.next.next == \old(this.next);
    public void push(T t) {
        var v = new List.Node<T>(t, next);
        //@ set v.owner = this;
        //@ assert this.allMine(this); // a lemma regarding allMine
        //@ assert v.size == this.size;
        //@ assert v.values == this.values;
        //@ assert v.links == this.links;
        this.next = v;
        //@ assert this.next.allMine(this); // a lemma regarding allMine
        //@ assert this.size == v.size + 1;
        //@ assert this.values == v.values.prepend(t);
        //@ assert this.links == v.links.prepend(v);
    }

    //@ public normal_behavior
    //@ ensures \result; 
    //@ model pure static public <T> boolean lemma(seq<T> s, T t1, T t2) { return (s.contains(t1) && !s.contains(t2) ==> t1 != t2); }
    
    /** Removes the first value from the list */
    //@ public normal_behavior
    //@   requires this.size > 0;
    //@   requires this.values.size() > 0;
    //@   assignable size, values, links, ownerFields;
    //@   ensures this.size == \old(size) - 1;
    //@   ensures this.values == \old(values).tail(1);
    //@   ensures this.links == \old(links).tail(1);
    //@   ensures next == \old(next.next);
    public void pop() {
        // (proved) lemmas to prompt unrolling
        //@ assert next.size == this.size - 1;
        //@ assert this.next.values.size() == this.values.size() - 1;
        //@ assert this.next.links.size() == this.links.size() - 1;
        //@ assert this.next.allMine(this.owner);
        //@ ghost nullable Link<T> nxx = this.next.next;
        //@ assert nxx != null ==> nxx.allMine(nxx.owner);
        //@ assert nxx != null && nxx.next != null ==> nxx.links == nxx.next.links.prepend(nxx.next);
        //@ assert nxx != null && nxx.next != null ==> this.links.contains(nxx.next);
        // !this.links.contains(this) is an invariant. Combined with the above, it implies the following.
        //@ assert nxx != null ==> (Object)this != nxx.next; // So that we know this.next.next.allMine is not affected by the change to this.next.
        this.next = this.next.next;
    }
    
    static class Node<T> extends Link<T> {

        /** Constructs a new link with given value and next field; for internal use only */
        //@ private normal_behavior
        //@   ensures this.next == next;
        //@   ensures this.value == value;
        //@ pure helper
        private Node(T value, /*@ helper nullable */ Node<T> next) {
            this.value = value;
            this.next = next;
        }
        
        //@ spec_public
        private T value; //@ in values;
        
        /** Returns the value from this link */
        //@ public normal_behavior
        //@   reads value;
        //@   ensures \result == value;
        //@ pure helper
        public T value() {
            return value;
        }
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
    //@ requires in.next != null && in.next.next != null;
    public static <Y> void testPush(List<Y> in, Y y) {
        //@ reachable;
        in.push(y);
        //@ reachable;
        //@ assert in.value(0) == y;
        //@ assert in.size == \old(in.size) + 1;
        //@ assert in.values.tail(1) == \old(in.values);
        //@ assert in.values == \old(in.values).prepend(y);
        //@ halt;
    }
    
    /** pushing a value and then retrieving it */
    //@ requires in.size > 0;
    public static <Y> void testPop(List<Y> in) {
        in.pop();
        //@ reachable;
        //@ assert in.size == \old(in.size) - 1;
        //@ assert in.values == \old(in.values).tail(1);
        //@ halt;
    }
    
    /** pushing a value and then retrieving it */
    //@ requires in.size > 0;
    public static <Y> void testRemove(List<Y> in) {
        in.remove(0);
        //@ reachable;
        //@ assert in.size == \old(in.size) - 1;
        //@ assert in.values == \old(in.values).tail(1);
        //@ halt;
    }
    
    /** pushing a value and then retrieving it */
    //@ requires in.size > 1;
    public static <Y> void testRemove1(List<Y> in) {
        in.remove(1);
        //@ reachable;
        //@ assert in.size == \old(in.size) - 1;
        //@ halt;
    }
    
    /** pushing a value and then retrieving it */
    //@ requires in.next != null && in.next.next != null;
    public static <Y> void testPushValue(List<Y> in, Y y, Y yy) {
        //@ reachable;
        in.push(y);
        //@ reachable;
        //@ assert in.value(0) == y;
        //@ assert in.size == \old(in.size) + 1;
        //@ assert in.values != \old(in.values);
        //@ reachable;
        in.push(yy);
        //@ reachable;
        //@ assert in.value(1) == y;
        //@ assert in.value(0) == yy;
    }
    
    /** pushing a value and then retrieving it */
    //@ requires in.size >= 2;
    public static <Y> void testPopValue(List<Y> in) {
        Y y = in.value(1);
        in.pop();
        //@ reachable;
        Y yy = in.value(0);
        //@ assert y == yy;
    }
    
    /** pushing and popping leaves the list unchanged */
    //@ requires in.next.next != null;
    public static <Y> void testPushPop(List<Y> in, Y y) {
        in.push(y);
        //@ reachable;
        //@ assert in.size == \old(in.size) + 1;
        //@ assert in.values != \old(in.values);
        in.pop();
        //@ reachable;
        //@ assert in.size == \old(in.size);
        //@ assert in.values == \old(in.values);
    }
    
    /** pushing and removing the zeroth element leaves the list unchanged */
    //@ requires in.next.next != null;
    public static <Y> void testPushRemove(List<Y> in, Y y) {
        in.push(y);
        //@ reachable;
        //@ assert in.size == \old(in.size) + 1;
        //@ assert in.values != \old(in.values);
        in.remove(0);
        //@ reachable;
        //@ assert in.size == \old(in.size);
        //@ assert in.values == \old(in.values);
    }
    
    /** pushing a value on one list does not change the other */
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 0;
    public static <Y> void testNI1(Y y, List<Y> in, List<Y> other) {
        in.push(y);
        //@ reachable;
        //@ assert in.values.tail(1) == other.values;
    }
    
    /** popping a value from one list does not change the other */
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 0;
    public static <Y> void testNI2(List<Y> in, List<Y> other) {
        //@ ghost seq<Y> oldvalues = in.values;
        in.pop();
        //@ reachable;
        //@ assert in.values == oldvalues.tail(1);
        //@ assert other.values == oldvalues;
    }
    
    /** removing a value (other than the 0th) from one list might change the other,
     * except when the owner invariant is used */
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 1;
    public static <Y> void testNI3(List<Y> in, List<Y> other) {
        //@ ghost seq<Y> oldvalues = in.values;
        in.remove(1);
        //@ reachable;
        //@ assert oldvalues.size - 1 == in.values.size;
        //@ assert other.values.size - 1 == in.values.size;   // Should not be provable without the owner invariant
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
    //@ requires in.next.value != y;
    /*@ model public static <Y> void testNI5(List<Y> in, List<Y> other, Y y) {
        reachable;
        ghost \bigint n = in.size;
        assert in.values.size() == n;
        assert in.values.size() == other.values.size();
        assert in.size == other.size;
        assert in.size == n;
        assert in.next.values == other.next.values;
        assert in.values[0] == other.values[0];
        in.next.value = y;
        assert in.next.values == other.next.values;
        assert in.values[0] != other.values[0];
        assert in.size == n;
        assert in.size == other.size;
        reachable;
        assert in.values != other.values;    // Should not be provable without the owner invariant
        reachable;
        assert in.values.tail(1) == other.values.tail(1);
        reachable;
    }
    @*/
}
