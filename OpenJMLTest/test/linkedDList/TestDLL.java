public class TestDLL {
    
    /** Implements a doubly-linked list with a sentinel head */
    static public class DLL<T> {
        static public class Link<T> {
            //@ public invariant next != null ==> this == next.previous;
            //@ public invariant previous != null ==> this == previous.next;
            //@ public invariant next != null ==> !next.links.contains(this);
            //@ public invariant links.size() == values.size();
            
            //@ model public seq<Link<T>> links;
            //@ represents links = next == null ? seq.of(this) : seq.of(this).append(next.links);
                        
            //@ model public seq<T> values;
            //@ represents values = next == null ? seq.of(value) : seq.of(value).append(next.values);

            //@ nullable
            public Link<T> next; //@ in links, values; // maps next.values \into values; maps next.links \into links;
            //@ nullable
            public Link<T> previous; //@ in links;
            
            //@ nullable
            public T value; //@ in values;
            
            //@ ensures value == v && next == null && previous == null;
            //@ ensures links.size() == 1;
            //@ ensures values.size() == 1;
            //@ pure
            public Link(T v) { 
                value = v;
            }
            
            // @ model public \bigint length;
            // @ represents length = (next == null ? (\bigint)1 : 1 + next.length);
            
            //@ requires 0 <= n <= links.length;
            //@ assigns \everything;
            // @ ensures values.sub(0,n) == \old(values).sub(0,n) && values.tail(n+1) == \old(values).tail(n);
            // @ ensures \fresh(links[n]) && values[n] == v;
            // @ ensures links.sub(0,n) == \old(links).sub(0,n) && links.tail(n+1) == \old(links).tail(n);
            //@ helper
            private void insert(int n, T v) {
                //@ assume next != null ==> this == next.previous;
                //@ assume previous != null ==> this == previous.next;
                //@ assume next != null ==> !next.links.contains(this);
                //@ assume links.size() == values.size();
                if (n == 0) {
                    var link = new Link<T>(v);
                    //@ assume \forall int i; 0 <= i < next.links.length; !\fresh(next.links[i]);
                    //@ assert next != null ==> !next.links.contains(link);
                    link.next = next;
                    if (next != null) link.next.previous = link;
                    //@ assert link.links.size() == this.links.size();
                    link.previous = this;
                    this.next = link;
                    //@ halt;
                } else {
                    //@ halt;
                    //@ assert 0 <= n-1;
                    //@ assert n-1 <= next.links.length;
                    next.insert(n-1, v);
                }
                //@ assert next != null;
                //@ assert next != null ==> this == next.previous;
                //@ assert previous != null ==> this == previous.next;
                //@ assume next != null ==> !next.links.contains(this);
           }
            
            //@ requires 0 <= n < links.length;
            //@ assigns values, links;
            //@ ensures values.sub(0,n) == \old(values).sub(0,n) && values.tail(n) == \old(values).tail(n+1);
            //@ ensures links.sub(0,n) == \old(links).sub(0,n) && links.tail(n) == \old(values).tail(n+1);
            public void remove(int n) {
                //@ assert this.next != null;
                if (n == 0) {
                    this.next.previous = this;
                    this.next = this.next.next;
                } else {
                    next.remove(n-1);
                }
            }
            
        }
        
        public DLL() {
            head = new Link<T>(null);
        }
        
        //@ non_null // This is a sentinel and not part of the actual list of values
        public Link<T> head; //@ in links, values; maps head.value \into values; maps head.next \into links;
        
        //@ model public seq<T> values;
        //@ represents values = head.values;
        
        //@ model public seq<Link<T>> links; //@ in values;
        //@ represents links = head.links;
        
        //@ requires head.links.length <= Integer.MAX_VALUE;
        //@ ensures \result == head.links.length -  1;
        //@ pure
        public int length() {
            int n = 0;
            var link = head;
            //@ ghost \bigint numlinks = head.links.length;
            //@ maintaining numlinks == n + link.links.length;
            //@ loop_writes n;
            //@ decreases numlinks - n;
            while (link.next != null) {
                //@ assert link.links == seq.of(link).append(link.next.links);
                //@ assert link.links.length == 1 + link.next.links.length;
                link = link.next;
                n++;
            }
            //@ assert n == numlinks - 1;
            return n;
        }
    
        //@ requires head.links.length <= Integer.MAX_VALUE;
        //@ old \bigint len = head.links.length;
        //@ reads head, head.*, links;
        //@ assignable head.*, head.links, head.values;
        //@ ensures values == seq.<T>of(v).append(\old(values));
        //@ ensures head.links.length == len + 1;
        public void push(T v) {
            head.insert(0, v);
        }

        //@ requires head.links.length <= Integer.MAX_VALUE;
        //@ old \bigint len = head.links.length;
        //@ reads head, head.*, links;
        //@ assignable head, head.*, head.links, head.values;
        //@ ensures values == \old(values).append(seq.of(v));
        //@ ensures head.links.length == len + 1;
        public void append(T v) {
            head.insert(length(), v);
        }

        //@ requires head.links.length <= Integer.MAX_VALUE;
        //@ old \bigint len = head.links.length;
        //@ requires len > 0;
        //@ reads head, head.*, links;
        //@ assignable head, head.*, head.links, head.values;
        //@ ensures links == \old(links).tail(1);
        //@ ensures values == \old(values).tail(1);
        //@ ensures head.links.length == len - 1;
        public void pop() {
            head.remove(0);
        }
    }
}