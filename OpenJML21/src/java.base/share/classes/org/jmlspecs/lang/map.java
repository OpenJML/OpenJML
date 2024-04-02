package org.jmlspecs.lang;

import java.util.*;

//@ immutable pure non_null_by_default
public class map<K,V> implements IJmlPrimitiveType, IJmlArrayLike {
    
    private HashMap<K,V> value = new HashMap<>();
    
    public map() { value = new HashMap<K,V>(); }

    public static <KK,VV> map<KK,VV> empty() { return new map<KK,VV>(); }
}
