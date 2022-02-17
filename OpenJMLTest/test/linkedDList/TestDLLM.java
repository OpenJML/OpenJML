public class TestDLLM {
    
    /** Implements a doubly-linked list with a sentinel head */
    static public class DLL<T> {
        static public class Link<T> {
            //@ public invariant next != null ==> this == next.previous;
            //@ public invariant previous != null ==> this == previous.next;
            //@ public invariant next != null ==> !next.links().contains(this);
            // @ public invariant links().size == values().size;
            //@ public invariant next != null ==> links().size == 1 + next.links().size;
            //@ public invariant next == null <==> links().size == 1;
            
            //@   ensures \result == (next == null ? seq.of(this) : seq.of(this).append(next.links()));
            //@ pure helper
            //@ model public seq<Link<T>> links();
             
            //@   ensures \result == (next == null ? seq.of(value) : seq.of(value).append(next.values()));
            //@ pure helper
            //@ model public seq<T> values();

            //@ nullable
            public Link<T> next; // @ in links, values; // maps next.values \into values; maps next.links \into links;
            //@ nullable
            public Link<T> previous; // @ in links;
            
            //@ nullable
            public T value; // @ in values;
            
            //@ ensures value == v && next == null && previous == null;
            //@ ensures links().size == 1;
            //@ ensures values().size == 1;
            //@ pure
            public Link(T v) { 
                value = v;
            }
            
            
            //@ requires 0 <= n < links().size;
            //@ assigns \everything;
            // @ ensures values.sub(0,n) == \old(values).sub(0,n) && values.tail(n+1) == \old(values).tail(n);
            // @ ensures \fresh(links[n]) && values[n] == v;
            // @ ensures links.sub(0,n) == \old(links).sub(0,n) && links.tail(n+1) == \old(links).tail(n);
            private void insert(int n, T v) {
                // @ assume links().size > 1 ==> next != null;
                // @ assume links().size == 1 ==> next == null;
                // @ assume next != null ==> this == next.previous;
                // @ assume previous != null ==> this == previous.next;
                // @ assume next != null ==> !next.links().contains(this);
                // @ assume links().size == values().size;
                if (n == 0) {
                    var link = new Link<T>(v);
                    //@ assume \forall int i; 0 <= i < next.links().size; !\fresh(next.links()[i]);
                    //@ assert next != null ==> !next.links().contains(link);
                    //@ halt;
                   link.next = next;
                    if (next != null) link.next.previous = link;
                    //@ assert link.links().size == this.links().size;
                    link.previous = this;
                    this.next = link;
                } else {
                    //@ halt;
                    //@ assert 0 <= n-1;
                    //@ assert n-1 <= next.links().size;
                    //@ halt;
                    next.insert(n-1, v);
                }
                //@ assert next != null;
                //@ assert next != null ==> this == next.previous;
                //@ assert previous != null ==> this == previous.next;
                //@ assume next != null ==> !next.links().contains(this);
           }
            
            //@ requires 0 <= n < links().size-1;
            //@ old seq<T> oldvalues = values();
            //@ old seq<Link<T>> oldlinks = links();
            //@ assigns \everything;
            // @ ensures values().sub(0,n) == oldvalues.sub(0,n) && values().tail(n) == oldvalues.tail(n+1);
            // @ ensures links().sub(0,n) == oldlinks.sub(0,n) && links().tail(n) == oldlinks.tail(n+1);
            public void remove(int n) {
                //@ assert this.next != null;
                if (n == 0) {
                    this.next.previous = this;
                    this.next = this.next.next;
                } else {
                    //@ halt;
                    next.remove(n-1);
                }
            }
            
        }
        
        public DLL() {
            head = new Link<T>(null);
        }
        
        //@ non_null // This is a sentinel and not part of the actual list of values
        public Link<T> head; // @ in links, values; maps head.value \into values; maps head.next \into links;
        
        //@ ensures \result == head.values();
        //@ model pure public seq<T> values();
        
        //@ ensures \result == head.links();
        //@ model public pure seq<Link<T>> links();
        
        //@ requires head.links().size <= Integer.MAX_VALUE;
        //@ ensures \result == head.links().size -  1;
        //@ pure
        public int length() {
            int n = 0;
            var link = head;
            //@ ghost \bigint numlinks = head.links().size;
            //@ maintaining numlinks == n + link.links().size;
            //@ loop_writes n;
            //@ decreases numlinks - n;
            while (link.next != null) {
                //@ assert link.links() == seq.of(link).append(link.next.links());
                //@ assert link.links().size == 1 + link.next.links().size;
                link = link.next;
                n++;
            }
            //@ assert n == numlinks - 1;
            return n;
        }
    
        //@ old \bigint len = head.links().size;
        //@ old seq<T> oldvalues = values();
        //@ old seq<Link<T>> oldlinks = links();
        //@ requires len <= Integer.MAX_VALUE;
        //@ assignable \everything;
        //@ ensures values() == seq.<T>of(v).append(oldvalues);
        //@ ensures head.links().size == len + 1;
        public void push(T v) {
            head.insert(0, v);
        }

        //@ old \bigint len = head.links().size;
        //@ old seq<T> oldvalues = values();
        //@ requires len <= Integer.MAX_VALUE;
        //@ assignable \everything;
        //@ ensures values() == oldvalues.append(seq.of(v));
        //@ ensures head.links().size == len + 1;
        public void append(T v) {
            head.insert(length(), v);
        }

        //@ old \bigint len = head.links().size;
        //@ old seq<Link<T>> oldlinks = links();
        //@ old seq<T> oldvalues = values();
        //@ requires 0 < len <= Integer.MAX_VALUE;
        //@ assignable \everything;
        //@ ensures links() == oldlinks.tail(1);
        //@ ensures values() == oldvalues.tail(1);
        //@ ensures head.links().size == len - 1;
        public void pop() {
            head.remove(0);
        }
    }
}