package org.jmlspecs.lang;
import java.util.*;
import org.jmlspecs.lang.internal.*;

//@ immutable pure 
public class seq<T> implements IJmlPrimitiveType, IJmlIntArrayLike {
    
    final java.util.List<T> value;
    
    private seq() { value = new ArrayList<>(); }
    
    public <T>seq<T> seq() { return new seq<T>(); }
    
    public bigint size() { return bigint.of(value.size()); }
    
    public bigint length() { return bigint.of(value.size()); }
    
    public T get(bigint i) { return value.get(i.intValue()); }

    public boolean isEmpty() { return value.isEmpty(); }
    
    static public <T> seq<T> empty() { return new seq<T>(); }

    static public <T> seq<T> of(T t) { var a = new seq<T>(); a.value.add(t); return a; }
    
    static public seq<Integer> of(int[] t) { var a = new seq<Integer>(); for (int k=0; k<t.length; k++) a.value.add(t[k]); return a; }
    
    @SuppressWarnings("unchecked")
    static public <T> seq<T> of(T ... t) { var a = new seq<T>(); a.value.addAll(java.util.Arrays.asList(t)); return a; }
    
    public static <T> boolean equals(seq<T> s, seq<T> ss) {
        if (s.size() != ss.size()) return false;
        for (long k = 0; k < s.size().longValue(); k++) if (s.get(bigint.of(k)) != ss.get(bigint.of(k))) return false;
        return true;
    }
    
    public <T> boolean contains(T v) {
        for (long k = 0; k < this.size().longValue(); k++) if (this.get(bigint.of(k)) == v) return true;
        return false;
    }
    
    public boolean eq(seq<T> s) { return equals(this,s); }
    
    public seq<T> insert(bigint j, T v) { var a = new seq<T>(); a.value.addAll(this.value.subList(0,j.intValue())); a.value.add(v); a.value.addAll(this.value.subList(j.intValue(), this.value.size())); return a; }

    public seq<T> add(T v) { var a = new seq<T>(); a.value.addAll(this.value); a.value.add(v); return a; }

    public seq<T> append(seq<T> s) { var a = new seq<T>(); a.value.addAll(this.value); a.value.addAll(s.value); return a; }

    public seq<T> prepend(T v) { var a = new seq<T>(); a.value.add(v); a.value.addAll(this.value); return a; }

    public seq<T> remove(bigint j) { var a = new seq<T>(); a.value.addAll(this.value.subList(0,j.intValue())); a.value.addAll(this.value.subList(j.intValue()+1,this.value.size())); return a; }

    public seq<T> put(bigint i, T v) { var a = new seq<T>(); a.value.addAll(this.value); a.value.set(i.intValue(), v); return a; }

    public seq<T> sub(bigint i, bigint j) { var a = new seq<T>(); a.value.addAll(this.value.subList(i.intValue(), j.intValue())); return a; }

    public seq<T> head(long i) { var a = new seq<T>(); a.value.addAll(this.value.subList(0, (int)i)); return a; }

    public seq<T> tail(long i) { var a = new seq<T>(); a.value.addAll(this.value.subList(this.value.size() - (int)i, this.value.size())); return a; }
}
