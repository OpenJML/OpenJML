

// A singly-linked list with the first element being a 'head' and not part of the list
// Specified with model fields
public class Linked<W> {
    
    //@ public model JMLDataGroup ownerFields;
    //@ ghost nullable public Linked<W> owner; //@ in ownerFields; maps next.ownerFields \into ownerFields;
    
    //@ model public seq<W> values; // sequence of values after the current Link, not including the current Link
    //@ public represents values = next == null ? seq.<W>empty() : next.values.prepend(next.value);
    //@ model public seq<Linked<W>> links;
    //@ public represents links = next == null ? seq.<Linked<W>>empty() : next.links.prepend(next);
    
    //@ public normal_behavior
    //@   reads this.owner, this.next.ownerFields, this.next;
    //@   ensures \result == (this.owner == owner && (next != null ==> next.allMine(owner)));
    //@ model pure helper public boolean allMine(Linked<W> owner);
    
    //@ public invariant this == this.owner ==> allMine(this);
    
    //@ model public \bigint size; 
    //@ public represents size = ((next == null) ? (\bigint)0 : 1 + next.size);
    //@ public invariant values.size() == size;
    //@ public invariant links.size() == size;
    //@ public invariant !links.contains(this);
    
    //@ nullable spec_public
    private Linked<W> next; //@ in size, values, links; 
    //@ maps next.values \into values; maps next.size \into size; maps next.links \into links;
    
    //@ public normal_behavior // only for demonstration purposes -- exposes representation
    //@ reads next;
    //@ ensures \result == next;
    //@ public model Linked<W> next();
    
    //@ nullable spec_public
    private W value; //@ in values;
    
    //@ public normal_behavior
    //@   ensures \result.values == seq.<T>empty();
    //@   ensures \result.size == 0;
    //@   ensures \result.value == null;
    //@   ensures \result.next == null;
    //@ pure
    public static <T> Linked<T> empty() {
        var n = new Linked<T>(null, null);
        n.owner = this;
        return n;
    }
    
    //@ private normal_behavior
    //@   ensures this.value == t;
    //@   ensures this.next == n;
    //@ pure helper
    private Linked(/*@ nullable */ W t, /*@ nullable */ Linked<W> n) {
        this.next = n;
        this.value = t;
    }
    
    //@ public normal_behavior
    //@   assignable size, values, links;
    //@   ensures \fresh(this.next);
    //@   ensures this.size == \old(size) + 1;
    //@   ensures this.values.equals(\old(values).prepend(t));
    //@   ensures this.links.equals(\old(links).prepend(this.next));
    //@   ensures this.next.value == t;
    //@   ensures this.next.next == \old(this.next);
    public void push(W t) {
        Linked<W> v = new Linked<W>(t, next);
        this.next = v;
        //@ set v.owner = this;
    }
    
    //@ public normal_behavior
    //@   requires next != null;
    //@   assignable size, values, links;
    //@   ensures this.size == \old(size) - 1;
    //@   ensures this.values.equals(\old(values).tail(1));
    //@   ensures this.links.equals(\old(links).tail(1));
    //@   ensures next == \old(next.next);
    public void pop() {
        this.next = this.next.next;
    }
    
    //@ public normal_behavior
    //@   requires 0 <= n < this.size;
    //@   assignable size, values, links;
    //@   ensures this.size == \old(this.size) - 1;
    //@   ensures this.values.equals(\old(values).tail(1));
    //@   ensures n == 0 ==> next == \old(next.next);
    //@   ensures n > 0 ==> next == \old(next);
    public void remove(int n) {
        if (n == 0) {
            this.next = this.next.next;
        } else {
            this.next.remove(n-1);
        }
    }
    
}

class Test {
    
    public static <Y> void test1(Linked<Y> in, Y y) {
        in.push(y);
        //@ assert in.size == \old(in.size) + 1;
        //@ assert in.values != \old(in.values);
        in.pop();
        //@ assert in.size == \old(in.size);
        //@ assert in.values == \old(in.values);
    }
    
    public static <Y> void test2(Y y) {
        var in = Linked.<Y>empty();
        //@ assert in.size == 0;
        //@ assert in.values.size() == 0;
        //@ assert in.values == seq.<Y>empty();
    }

    public static <Y> void test3(Linked<Y> in, Y y) {
        in.push(y);
        //@ assert in.size == \old(in.size) + 1;
        //@ assert in.values != \old(in.values);
        in.remove(0);
        //@ assert in.size == \old(in.size);
        //@ assert in.values == \old(in.values);
    }
    
    //@ requires in != other;
    //@ requires in.values == other.values;
    public static <Y> void test4(Y y, Linked<Y> in, Linked<Y> other) {
        // @ assume in.size == other.size;
        in.push(y);
        //@ assert in.values.tail(1) == other.values;
    }
    
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 0;
    public static <Y> void test5(Linked<Y> in, Linked<Y> other) {
        // @ assume in.size == other.size;
        //@ ghost seq<Y> oldvalues = in.values;
        in.pop();
        //@ assert oldvalues.tail(1) == in.values;
        //@ assert in.values == other.values.tail(1);
    }
    
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 1;
    public static <Y> void test6(Linked<Y> in, Linked<Y> other) {
        //@ ghost seq<Y> oldvalues = in.values;
        in.remove(1);
        //@ assert oldvalues.size - 1 == in.size;
        //@ assert other.values.size - 1 == in.size;
    }
    
    //@ requires in != other;
    //@ requires in.values == other.values;
    //@ requires in.size > 1;
    /*@ model public static <Y> void test7(Linked<Y> in, Linked<Y> other, Y y) {
        assume in.next.value != y;
        assert in.size == other.size;
        in.next().value = y;
        assert in.size == other.size;
        assert in.values != other.values;
        assert in.values.tail(1) == other.values.tail(1);
    }
    @*/
    
    //@ requires in != other;
    //@ requires in.size > 1;
    public static <Y> void test8(Linked<Y> in, Linked<Y> other) {
        //@ assert in.next != other.next;
    }
    

}