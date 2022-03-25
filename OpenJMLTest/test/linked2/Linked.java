
// A singly-linked list with the first element being a 'head' and not part of the list
// Specified with model methods
public class Linked<W> {
    //@ public normal_behavior
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
    
    //@ nullable
    public Linked<W> next;//@ in nextFields; maps next.nextFields \into nextFields;
    //@ nullable
    public W value; //@ in valueFields; maps next.valueFields \into valueFields;
    
    //@ public normal_behavior
    //@   ensures \result.value == null;
    //@   ensures \result.next == null;
    //@   ensures \result.values() == seq.<W>empty();
    //@   ensures \result.size() == 0;
    //@ pure
    public static <W> Linked<W> empty() {
        return new Linked(null, null);
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
        Linked v = new Linked(t, next);
        //@ assert nn == (this.next == null ? -1 : this.next.size());
        // @ assert this.next != null ==> v.values() == oldvalues;
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
        this.next = this.next.next;
        //@ assert this.size() == (this.next == null ? 0 : this.next.size() + 1);
        //@ assert this.size() == \old(this.size()) - 1;
    }
    
    //@ public normal_behavior
    //@   requires 0 <= n < this.size();
    //@   old \bigint oldsize = this.size();
    //@   old seq<W> oldvalues = this.values();
    //@   assignable next, nextFields;
    //@   ensures this.size() == oldsize - 1;
    // @   ensures this.values() == oldvalues.tail(1); // FIXME
    public void remove(int n) {
        //@ ghost \bigint nnn = (this.next.next == null ? 0 : this.next.next.size() + 1);
        //@ ghost \bigint nn = this.next.size();
        if (n == 0) {
            this.next = this.next.next;
            //@ assert nn == (this.next == null ? 0 : this.next.size() + 1);
            //@ assert this.size() == nn;
        } else {
            this.next.remove(n-1);
            //@ assert this.size() == nn;
        }
        //@ assert this.size() == nn;
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