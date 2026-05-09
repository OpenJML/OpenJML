package org.jmlspecs.lang.internal;

import org.jmlspecs.lang.IJmlPrimitiveType;
import org.jmlspecs.lang.IJmlIntArrayLike;

//@ immutable no_state 
public class array<T> implements IJmlPrimitiveType, IJmlIntArrayLike {
    
    private final T[] value;
    public final bigint length;
    
    private array() { value = null; length = bigint.zero; }
    private array(T[] v) { value = v; length = bigint.of(v.length); }
    
    public static <TT> array<TT> empty() { return new array<TT>(); }

    @SafeVarargs
    @SuppressWarnings({"varargs","unchecked"})
    public static <TT> array<TT> of(TT ... data) {
        return new array<TT>(data);
    }

    private array<T> copy() { 
        if (value == null) return array.<T>empty();
        return array.<T>of(java.util.Arrays.copyOf(value, value.length));
    }

    public T get(bigint i) {
        if (value == null || i.lt(bigint.zero) || i.ge(length)) throw new java.lang.ArrayIndexOutOfBoundsException("get: " + i + " for length " + length);
        return value[i.intValue()];
    }
    
    public T getUnchecked(bigint i) {
        return value[i.intValue()];
    }
    
    public array<T> put(bigint i, T v) {
        if (value == null || i.lt(bigint.zero) || i.ge(length)) throw new java.lang.ArrayIndexOutOfBoundsException("put: " + i + " for length " + length);
        var c = copy();
        c.value[i.intValue()] = v;
        return c;
    }
    
    public array<T> subarray(bigint i, bigint j) {
        if (!(bigint.zero.le(i) && i.le(j) && j.le(this.length))) throw new java.lang.ArrayIndexOutOfBoundsException("subarray: " + i + " " + j + " for length " + length);
        return array.<T>of(java.util.Arrays.copyOfRange(value, i.intValue(), j.intValue()));
    }
    
    public boolean eq(array<T> a) { 
        if (length.ne(a.length)) return false;
        if (length.eq(bigint.zero)) return true;
        for (int i=0; i < value.length; ++i) {
            if (value[i] != a.value[i]) return false;
        }
        return true;
    }
    
    public boolean ne(array<T> a) {
        return !eq(a);
    }
    
    public T[] value() { return value; }
    
    public int hashCode() {
        return value == null ? 0 : java.util.Arrays.hashCode(value);
    }
    
    public boolean equals(array<T> a) {
        return eq(a);
    }
    
    @SuppressWarnings({"unchecked","rawtypes"})
    public boolean equals(Object o) {
        return o instanceof array a && eq(a);
    }

}
