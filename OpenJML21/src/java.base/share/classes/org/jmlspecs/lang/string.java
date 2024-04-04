package org.jmlspecs.lang;

import org.jmlspecs.lang.internal.bigint;
// This file provides RAC implementations

//@ immutable spec_pure
public final class string implements IJmlPrimitiveType, IJmlIntArrayLike {

    private String racValue = "";
    
    private string(String s) {
        racValue = s;
    }
    
    static public string string(String s) {
        return new string(s);
    }
    
    public char get(bigint ii) { // FIXME - change to bigint eventually
        int i = ii.intValue();
        if (i < 0 || i >= racValue.length()) return (char)0;
        return racValue.charAt(i);
    }
    
    public string put(bigint ii, char v) {
        int i = ii.intValue();
        return string(racValue.substring(0,i) + v + racValue.substring(i+1));
    }
    
    static public string of(String s) {
        return string(s);
    }

    public static string empty() {
        return string("");
    }
    
    public bigint length() {
        return bigint.of(racValue.length());
    }
    
    public bigint size() {
        return bigint.of(racValue.length());
    }
    
    public boolean isEmpty() {
        return racValue.isEmpty();
    }
    
    public static boolean eq(string s, string ss) {
        return s.racValue.equals(ss.racValue);
    }
 
    public boolean eq(string s) {
        return this.racValue.equals(s.racValue);
    }
    
    public boolean ne(string s) {
        return !eq(s);
    }
    
    public boolean equals(Object o) { throw new UnsupportedOperationException(); }
    public int hashCode() { throw new UnsupportedOperationException(); }

    
    public static string concat(string s, string ss) {
        return string(s.racValue + ss.racValue);
    }
 
    public string add(char v) {
        return string(racValue.concat(String.valueOf(v)));
    }

    public string append(string s) {
        return concat(this,s);
    }

    public string insert(bigint ii, char v) {
        int i = ii.intValue();
        return string(racValue.substring(0,i) + v + racValue.substring(i));
    }

    public string remove(bigint ii) {
        int i = ii.intValue();
        return string(racValue.substring(0,i) + racValue.substring(i+1));
    }

    public string substring(bigint start, bigint end) {
        return string(racValue.substring(start.intValue(), end.intValue()));
    }
}
