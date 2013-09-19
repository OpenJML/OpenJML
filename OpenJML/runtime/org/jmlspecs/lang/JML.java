package org.jmlspecs.lang;

public class JML {

    //@ model pure public static Class<?> erasure(\TYPE type) { return null; }
    
    //@ public normal_behavior
    //@ ensures \result;
    //@ pure helper
    public static boolean informal(String s) {
        return true;
    }
}
