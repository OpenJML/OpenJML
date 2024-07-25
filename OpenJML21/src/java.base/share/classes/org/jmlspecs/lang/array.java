package org.jmlspecs.lang;

import org.jmlspecs.lang.internal.bigint;

//@ immutable no_state 
public class array<T> implements IJmlPrimitiveType, IJmlIntArrayLike {
    
    private T[] value;
    
    private array() { value = null; }
    private array(T[] v) { value = v; }
    
    public static <TT> array<TT> empty() { return new array<TT>(); }

    public static <TT> array<TT> of(TT[] data) { return new array<TT>(data); }

    public array<T> copy() { 
        if (value == null) return array.<T>empty();
        return array.<T>of(java.util.Arrays.copyOf(value, value.length));
    }

    public T get(bigint i) {
        return value[i.intValue()];
    }
    
    public array<T> put(bigint i, T v) {
        var c = copy();
        c.value[i.intValue()] = v;
        return c;
    }
    
    public boolean eq(array<T> a) { 
        if (value == null && a.value == null) return true;
        if (value == null || a.value == null) return false;
        if (value.length != a.value.length) return false;
        for (int i=0; i<value.length; ++i) {
            if (value[i] != a.value[i]) return false;
        }
        return true;
    }
    
    public boolean ne(array<T> a) {
        return !eq(a);
    }
    
    public T[] value() { return value; }
}
