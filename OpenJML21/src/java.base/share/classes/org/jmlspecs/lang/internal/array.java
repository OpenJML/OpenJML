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
        //System.out.println("OF " + data.getClass() + " " + data.length);
        // FIXME - it appears that the wrapping of the varargs into a new TT[]{} call and making that a new argument for 'of(TT ...)'
        // is followed by an implicit further cast of the TT[] into an Object and then into a singleton Object[]
        if (data.length == 1 && data[0].getClass().isArray()) data = (TT[])data[0];
        //System.out.println("OF=Z " + data.getClass() + " " + data.length);
        return new array<TT>(data);
    }
//    public static <TT> array<TT> of(TT[] data, int len) { return new array<TT>(data); }

    public array<T> copy() { 
        if (value == null) return array.<T>empty();
        return array.<T>of(java.util.Arrays.copyOf(value, value.length));
    }

    public T get(bigint i) {
        if (value == null || i.lt(bigint.zero) || i.ge(length)) throw new java.lang.ArrayIndexOutOfBoundsException(i + " vs. " + length);
        return value[i.intValue()];
    }
    
    public array<T> put(bigint i, T v) {
        if (value == null || i.lt(bigint.zero) || i.ge(length)) throw new java.lang.ArrayIndexOutOfBoundsException(i + " vs. " + length);
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
    
    public int hashCode() {
        return value == null ? 0 : value.hashCode();
    }
    
    public boolean equals(Object o) {
        throw new UnsupportedOperationException("\\array<T>.equals not supported; use == or .eq instead");
    }

}
