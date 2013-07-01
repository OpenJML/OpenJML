package org.jmlspecs.lang;

public class JML {

    //@ model pure public static Class<?> erasure(\TYPE type);
    
    //@ public normal_behavior
    //@ ensures \result;
    //@ pure
    public static boolean informal(String s) {
        return true;
    }
}
