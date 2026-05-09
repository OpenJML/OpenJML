package org.jmlspecs.lang.internal;
import java.util.*;
import org.jmlspecs.lang.IJmlPrimitiveType;
import org.jmlspecs.lang.IJmlIntArrayLike;

//@ immutable no_state 
public class seq<T> implements IJmlPrimitiveType, IJmlIntArrayLike {
    
    final private java.util.List<T> value;
    final public bigint length;
    
    private seq() { value = new ArrayList<T>(); length=bigint.of(value.size()); }
    private seq(T[] a) { value = java.util.Arrays.asList(a); length=bigint.of(value.size()); }
    private seq(List<T> a) { value = a; length=bigint.of(value.size()); }
    
    public bigint length() { return bigint.of(value.size()); }
    
    static public <T> seq<T> empty() { return new seq<T>(); }

    static public seq<Integer> of(int[] t) { var al = new ArrayList<Integer>(); for (int k=0; k<t.length; k++) al.add(t[k]); return new seq<Integer>(al); }
    
    @SuppressWarnings("unchecked")
    static public <T> seq<T> of(T ... data) { 
        return new seq<T>(data);
    }
    
    public boolean isEmpty() { return value.isEmpty(); }
    
    public T get(bigint i) { 
        if (i.lt(bigint.zero) || i.ge(length)) throw new IndexOutOfBoundsException("\\seq.get: " + i + " vs. " + length);
        return value.get(i.intValue());
    }

    public boolean equals(seq<T> s) {
        return this.eq(s);
    }
    
    @SuppressWarnings({"rawtypes","unchecked"})
    public boolean equals(Object o) {
        return o instanceof seq s && this.equals(s);
    }
    
    public int hashCode() {
        return value.hashCode();
    }
    
    public <T> boolean contains(T v) {
        for (long k = 0; k < this.length().longValue(); k++) if (this.get(bigint.of(k)) == v) return true;
        return false;
    }
        
    public boolean eq(seq<T> s) {
        if (this.length.ne(s.length)) return false;
        for (int k = 0; k < s.length().intValue(); k++) {
            if (s.value.get(k) != this.value.get(k)) return false;
        }
        return true;
    }
    
    public boolean ne(seq<T> s) { return !eq(s); }
    
    public seq<T> insert(bigint j, T v) { 
        if (j.lt(bigint.zero) || j.gt(length)) throw new IndexOutOfBoundsException("\\seq.put: " + j + " vs. " + length);
        var al = new ArrayList<T>(); 
        al.addAll(this.value.subList(0,j.intValue())); 
        al.add(v); 
        al.addAll(this.value.subList(j.intValue(), this.value.size())); 
        return new seq<T>(al);
    }

    public seq<T> prepend(T v) { return insert(bigint.zero, v); }

    public seq<T> prepend(seq<T> s) { var al = new ArrayList<T>(); al.addAll(s.value);al.addAll(this.value); return new seq<T>(al); }

    public seq<T> append(seq<T> s) { var al = new ArrayList<T>(); al.addAll(this.value);al.addAll(s.value); return new seq<T>(al); }

    public seq<T> append(T v) { return insert(length, v); }

    public seq<T> remove(bigint j) { 
        if (j.lt(bigint.zero) || j.ge(length)) throw new IndexOutOfBoundsException("\\seq.remove: " + j + " vs. " + length);
        var al = new ArrayList<T>();
        al.addAll(this.value.subList(0,j.intValue())); 
        al.addAll(this.value.subList(1+j.intValue(), this.value.size())); 
        return new seq<T>(al); 
    }

    public seq<T> put(bigint i, T v) {
        if (i.lt(bigint.zero) || i.ge(length)) throw new IndexOutOfBoundsException("\\seq.put: " + i + " vs. " + length);
        var al = new ArrayList<T>(); 
        al.addAll(this.value.subList(0,i.intValue())); 
        al.add(v); 
        al.addAll(this.value.subList(1+i.intValue(), this.value.size())); 
        return new seq<T>(al);
    }

    public seq<T> subseq(bigint i, bigint j) { 
        if (i.lt(bigint.zero) || j.lt(i) || length.lt(j)) throw new IndexOutOfBoundsException("\\seq.subseq: " + i + " " + j + " vs. " + length);
        var a = new seq<T>(this.value.subList(i.intValue(), j.intValue()));
        return a;
    }

    public T head() {
        if (isEmpty()) throw new IndexOutOfBoundsException("\\seq.head: sequence is empty");
        return value.get(0);
    }

    public seq<T> head(bigint i) { 
        return subseq(bigint.zero, i);
    }

    public seq<T> tail() { return subseq(bigint.one, length); }

    public seq<T> tail(bigint i) { return subseq(i, length); }
    
    public String toString() {
        var s = new StringBuilder();
        s.append("[");
        for (int i = 0; i < value.size(); i++) {
            if (i > 0) s.append(",");
            s.append(value.get(i).hashCode());
        }
        s.append("]");
        return s.toString();
    }
}
