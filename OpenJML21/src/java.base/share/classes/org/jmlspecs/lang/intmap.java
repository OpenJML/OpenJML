package org.jmlspecs.lang;

import java.util.*;
import org.jmlspecs.lang.internal.bigint;
import java.math.BigInteger;

/** value-based map from \bigint to V */

//@ immutable pure 
public class intmap<V> implements IJmlPrimitiveType, IJmlIntArrayLike {
    
    private Map<BigInteger, V> value = new HashMap<>();
    
    private intmap() { value = new HashMap<BigInteger,V>(); }
    private intmap(HashMap<BigInteger,V> data) { value = data; }
    
    public static <VV> intmap<VV> empty() { return new intmap<VV>(); }
    
    public boolean has(bigint i) { return value.get(i.bigValue()) != null; }

    public V get(long i) { return value.get(BigInteger.valueOf(i)); }
    public V get(bigint i) { return value.get(i.bigValue()); }
    public V get(BigInteger i) { return value.get(i); }
    
//    public intmap<V> put(BigInteger i, V t) {
//        var copy = new HashMap<BigInteger,V>(value);
//        copy.put(i, t);
//        return new intmap<V>(copy);
//    }
    
    public intmap<V> put(bigint i, V t) {
        var copy = new HashMap<BigInteger,V>(value);
        copy.put(i.bigValue(), t);
        return new intmap<V>(copy);
    }
    
    public intmap<V> put(long i, V t) {
        return put(bigint.of(i), t);
    }
}
