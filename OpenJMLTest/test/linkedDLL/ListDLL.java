// openjml --esc $@
/** This file contains a worked (specified and verified) example of a doubly-linked list using JML and OpenJML. 
 * It is intended to illustrate techniques that can be used for other simple recursive data structures. 
 * This example uses model fields.
 * 
 * A list of values of type T is an instance of the public class ListDLL<T>. The actual links are instances of the non-public
 * nested class Node<T>; both classes inherit from Link<T>, which contains common functionality. The linked-list is formed
 * by the typical chain of 'next' and 'prev' field references, with a null reference at the end of the list. The starting point, the List
 * object, is not a part of the abstract list.
 * 
 */

/** Parent class for ListDLL and Node containing the 'next' field and common functionality */
class Link<T> {

    //@ public model JMLDataGroup ownerFields;
    //@ ghost helper nullable public ListDLL<T> owner; //@ in ownerFields; maps next.ownerFields \into ownerFields;

    //@ model public seq<T> values; // sequence of values after the current Link, not including the current Link
    //@ public represents values = next == null ? seq.<T>empty() : next.values.prepend(next.value);

    //@ model public seq<Link<T>> links;
    //@ public represents links = next == null ? seq.<Link<T>>empty() : next.links.prepend(next);

    //@ model public seq<Link<T>> prevlinks;
    //@ public represents prevlinks = next == null ? seq.<Link<T>>empty() : next.links.prepend(next.prev);

    // True if my owner is the argument and all nodes after me have the argument as their owners.
    //@ public normal_behavior
    //@   reads this.owner, this.next.ownerFields, this.links;
    //@   ensures \result == (this.owner == owner && (next != null ==> next.allMine(owner)));
    //@ model pure helper public boolean allMine(ListDLL<T> owner);

    //@ public normal_behavior
    //@   reads this.links, this.prevlinks;
    //@   ensures \result <==> (this.next != null ==> (this.next.prev == this && this.next.goodLinksForward()));
    //@ model pure helper public boolean goodLinksForward();
    
    //@ model public \bigint size; 
    //@ public represents size = ((next == null) ? 0 : 1 + next.size);
    
    //@ public invariant this.owner != null && allMine(this.owner);
    //@ public invariant this.goodLinksForward();
    //@ public invariant values.size() == size;
    //@ public invariant links.size() == size;
    //@ public invariant !links.contains(this);

    //@ nullable spec_public
    protected ListDLL.Node<T> next; //@ in size, values, links, prevlinks, ownerFields; 
    //@ maps next.values \into values; maps next.next \into values; maps next.next.values \into values;
    //@ maps next.size \into size; maps next.next \into size; maps next.next.size \into size;
    //@ maps next.links \into links; maps next.next.links \into links; maps next.next.links \into links;
    //@ maps next.prev \into prevlinks; maps next.next.prev \into prevlinks; maps next.prevlinks \into prevlinks;
    
    //@ nullable spec_public helper
    protected Link<T> prev;

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
    //@   {| requires next.next != null; assignable size, values, links, ownerFields, next.size, next.next.prev; also requires next.next == null; assignable size, values, links, ownerFields, next.size; |}
    //@   ensures this.size == \old(this.size) - 1;
    //@   ensures this.values.size() == \old(this.values.size()) - 1;
    //@   ensures this.links.size() == \old(this.links.size()) - 1;
    //@   ensures n == 0 ==> values == \old(values).tail(1);
    //@   ensures n == 0 ==> links == \old(links).tail(1);
    //@   ensures n == 0 ==> next == \old(next.next);
    //@   ensures n == 0 ==> values == \old(values).tail(1);
    //@   ensures n > 0 ==> next == \old(next);
    public void remove(int n) {
        //@ ghost \bigint newsize = next.size;
        if (n == 0) {
            //@ assert this.allMine(this.owner);
            //@ assert this.next.allMine(this.owner);
            //@ assert this.next.next != null ==> this.next.next.allMine(this.next.owner);
            //@ assert this.goodLinksForward();
            //@ assert this.next.goodLinksForward();
            //@ ghost seq<T> newvalues = this.next.values;
            //@ ghost seq<Link<T>> newlinks = this.next.links;
            if (this.next.next != null) {
                //@ assert this.next.next.goodLinksForward();
                //@ assert this.next.next.prev == this.next;
                //@ assert this.next.next.prev.next == this.next.next;
                //@ assert this.next.next.values == newvalues.tail(1);
                //@ assert this.next.next.links == newlinks.tail(1);
                //@ assert this.next.next.size == newsize - 1;
                //@ assert this.next.next.allMine(this.next.owner);
                this.next.next.prev = this;
                //@ assert this.next.next.goodLinksForward();
                //@ assert this.next.next.size == newsize - 1;
                //@ assert this.next.next.allMine(this.next.owner);
                //@ assert this.next.next.values == newvalues.tail(1);
                //@ assert this.next.next.links == newlinks.tail(1);
                this.next = this.next.next;
                //@ assert this.next.prev == this && this.next.goodLinksForward();
                //@ assert this.goodLinksForward();
                //@ assert this.next.size == newsize - 1;
                //@ assert this.size == newsize;
                //@ assert this.next.allMine(this.next.owner);
                //@ assert this.next.values == newvalues.tail(1);
                //@ assert this.values == newvalues;
                //@ assert this.next.links == newlinks.tail(1);
                //@ assert this.links == newlinks;
                //@ reachable;
            } else {
                this.next = this.next.next;
                //@ assert this.goodLinksForward();
                //@ assert this.size == newsize;
                //@ assert this.allMine(this.owner);
                //@ assert this.values == newvalues;
                //@ assert this.links == newlinks;
                //@ reachable;
            }
            //@ assert this.next != null ==> this.next.goodLinksForward();
            //@ assert this.goodLinksForward();
            //@ assert this.size == newsize;
            //@ assert this.allMine(this.owner);
            //@ assert this.values == newvalues;
            //@ assert this.links == newlinks;
        } else {
            //@ assert this.next.goodLinksForward();
            //@ assert this.next.size == newsize;
            this.next.remove(n-1);
            //@ reachable; 
            //@ assert this.next.goodLinksForward();
            //@ assert this.next.allMine(this.next.owner);
            //@ assert this.next.size == newsize - 1;
            //@ assert this.next.values.size() == newsize - 1;
            //@ assert this.next.links.size() == newsize - 1;
            //@ assert this.goodLinksForward();
            //@ assert this.size == newsize;
            //@ assert this.values.size() == newsize;
            //@ assert this.links.size() == newsize;
            //@ assert allMine(this.owner);
        }
        //@ assert this.goodLinksForward();
        //@ assert allMine(this.owner);
        //@ assert this.size == newsize;
        //@ assert this.values.size() == newsize;
        //@ assert this.links.size() == newsize;
    }
}

public class ListDLL<T> extends Link<T> {
    
    //@ public invariant this.owner == this;
    //@ public invariant this.prev == null;
    
    /** Creates an empty list -- just an anchor node with null 'next' field */
    //@ public normal_behavior
    //@   ensures \result.values == seq.<TT>empty();
    //@   ensures \result.size == 0;
    //@   ensures \result.links == seq.<Link<TT>>empty();
    //@   ensures \result.next == null;
    //@   ensures \result.owner == \result;
    //@ pure
    public static <TT> ListDLL<TT> empty() {
        return new ListDLL<TT>();
    }
    
    //@ private normal_behavior
    //@   ensures this.next == null;
    //@   ensures this.prev == null;
    //@   ensures this.owner == this;
    //@ pure
    private ListDLL() {
        this.next = null;
        this.prev = null;
        //@ set this.owner = this;
    }
    
    /** Pushes a new value onto the front of the list */
    //@ public normal_behavior
    //@   assignable size, values, links, ownerFields;
    //@   ensures this.size == \old(size) + 1;
    //@   ensures this.values == \old(values).prepend(t);
    //@   ensures this.links == \old(links).prepend(this.next);
    //@   ensures \fresh(this.next);
    //@   ensures this.next.value == t;
    //@   ensures this.next.next == \old(this.next);
    public void push(T t) {
        //@ assert allMine(this);
        //@ assert this.next != null ==> this.next.allMine(this);
        //@ assert next != null ==> next.goodLinksForward();
        var v = new ListDLL.Node<T>(t, next, this);
        //@ assert next != null ==> next.goodLinksForward();
        //@ assert v.owner == this;
        //@ assert v.next != null ==> v.next.allMine(this);
        //@ assert v.allMine(this);
        if (next != null) next.prev = v;
        //@ assert next != null ==> next.goodLinksForward();
        //@ assert v.goodLinksForward();
        //@ assert v.next == this.next;
        //@ assert (v.owner == this && (v.next != null ==> v.next.allMine(v.owner)));
        //@ assert v.allMine(this);
        this.next = v;
        //@ assert v.goodLinksForward();
        //@ assert this.goodLinksForward();
        //@ assert this.next.allMine(this); // a lemma regarding allMine
        //@ assert this.size == v.size + 1;
        //@ assert this.values == v.values.prepend(t);
        //@ assert this.links == v.links.prepend(v);
    }
    
    /** Removes the first value from the list */
    //@ public normal_behavior
    //@   requires this.size > 0;
    //@   requires this.values.size() > 0;
    //@   {| requires next.next == null; assignable ownerFields, size, values, links, prevlinks; also requires next.next != null; assignable ownerFields, size, values, links, prevlinks, next.next.prev; |}
    //@   ensures this.size == \old(size) - 1;
    //@   ensures this.values == \old(values).tail(1);
    //@   ensures this.links == \old(links).tail(1);
    //@   ensures next == \old(next.next);
    public void pop() {
        //@ assert this.owner == this && this.allMine(this.owner);
        //@ assert this.next.owner == this && this.next.allMine(this.owner);
        //@ assert this.next.next != null ==> this.next.next.allMine(this.next.owner);
        //@ assert this.goodLinksForward();
        //@ assert this.next.goodLinksForward();
        //@ assert this.next.next != null ==> this.next.next.goodLinksForward();
        //@ ghost var n = this.next;
        //@ assert (n.next != null) ==> n.next.prev == n;
        //@ assert (n.next != null) ==> n.next.prev.next == n.next;
        //@ ghost \bigint newsize = next.size;
        //@ assert this.next.next != null ==> next.next.size == newsize - 1;
        //@ ghost seq<T> newvalues = this.next.values;
        //@ assert this.next.next != null ==> this.next.next.values == newvalues.tail(1);
        //@ ghost seq<Link<T>> newlinks = this.next.links;
        //@ assert this.next.next != null ==> this.next.next.links == newlinks.tail(1);
        //@ reachable;
        if (this.next.next != null) {
            //@ assert this.next.next.allMine(this.next.owner);
            //@ assert this.next.next.goodLinksForward();
            //@ assert this.next.next.next != null ==> this.next.next.next.goodLinksForward();
            this.next.next.prev = this;
            //@ assert this.next.next.next != null ==> this.next.next.next.goodLinksForward();
            //@ assert this.next.next.goodLinksForward();
            //@ assert this.next.next.size == newsize - 1;
            //@ assert this.next.next.allMine(this.next.owner);
            //@ assert this.next.next.values == newvalues.tail(1);
            //@ assert this.next.next.links == newlinks.tail(1);
            this.next = this.next.next;
            //@ assert this.next.prev == this && this.next.goodLinksForward();
            //@ assert this.goodLinksForward();
            //@ assert this.next.size == newsize - 1;
            //@ assert this.size == newsize;
            //@ assert this.next.allMine(this.next.owner);
            //@ assert this.next.values == newvalues.tail(1);
            //@ assert this.values == newvalues;
            //@ assert this.next.links == newlinks.tail(1);
            //@ assert this.links == newlinks;
            //@ reachable;
        } else {
            this.next = this.next.next;
            //@ assert this.goodLinksForward();
            //@ assert this.size == newsize;
            //@ assert this.allMine(this.owner);
            //@ assert this.values == newvalues;
            //@ assert this.links == newlinks;
            //@ reachable;
        }
        //@ assert this.next != null ==> this.next.goodLinksForward();
        //@ assert this.goodLinksForward();
        //@ assert this.size == newsize;
        //@ assert this.allMine(this.owner);
        //@ assert this.values == newvalues;
        //@ assert this.links == newlinks;
    }
    
    static class Node<T> extends Link<T> {

        /** Constructs a new link with given value and next field; for internal use only */
        //@ private normal_behavior
        //@   requires next != prev;
        //@   ensures this.next == next;
        //@   ensures this.prev == prev;
        //@   ensures this.value == value;
        //@   ensures this.owner == prev.owner;
        //@ pure helper
        private Node(T value, /*@ helper nullable */ Node<T> next, /*@ helper */ Link<T> prev) {
            this.value = value;
            this.next = next;
            this.prev = prev;
            //@ set this.owner = prev.owner;
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
        var in = ListDLL.<Y>empty();
        //@ assert in.size == 0;
        //@ assert in.values.size() == 0;
        //@ assert in.values == seq.<Y>empty();
    }

    /** pushing a value and then retrieving it */
    //@ requires in.next.next != null;
    public static <Y> void testPushValue(ListDLL<Y> in, Y y, Y yy) {
        in.push(y);
        //@ reachable;
        //@ assert in.value(0) == y;
        //@ assert in.size == \old(in.size) + 1;
        //@ assert in.values != \old(in.values);
        in.push(yy);
        //@ reachable;
        //@ assert in.value(1) == y;
        //@ assert in.value(0) == yy;
    }
    
    /** popping a list */
    //@ requires in.size >= 2;
    public static <Y> void testPopValue(ListDLL<Y> in) {
        Y y = in.value(1);
        in.pop();
        //@ reachable;
        Y yy = in.value(0);
        //@ assert y == yy;
    }
    
    /** pushing and popping leaves the list unchanged */
    //@ requires in.next.next != null;
    public static <Y> void testPushPop(ListDLL<Y> in, Y y) {
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
    public static <Y> void testPushRemove(ListDLL<Y> in, Y y) {
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
    public static <Y> void testNI1(Y y, ListDLL<Y> in, ListDLL<Y> other) {
        in.push(y);
        //@ reachable;
        //@ assert in.values.tail(1) == other.values;
    }
    
    /** popping a value from one list does not change the other */
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 0;
    public static <Y> void testNI2(ListDLL<Y> in, ListDLL<Y> other) {
        //@ assert in.size == other.size;
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
    public static <Y> void testNI3(ListDLL<Y> in, ListDLL<Y> other) {
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
    public static <Y> void testNI4(ListDLL<Y> in, ListDLL<Y> other) {
        //@ assert in.next.owner == in;
        //@ assert other.next.owner == other;
        //@ assert in.next != other.next;    // Should not be provable without the owner invariant
    }
    
    /** using rep-exposure to change a value still does not change the other list if the owner invariant is used */
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 1;
    //@ requires in.next.value != y;
    /*@ model public static <Y> void testNI5(ListDLL<Y> in, ListDLL<Y> other, Y y) {
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
