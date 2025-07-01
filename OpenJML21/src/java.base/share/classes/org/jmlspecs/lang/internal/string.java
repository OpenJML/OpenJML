package org.jmlspecs.lang.internal;

import org.jmlspecs.lang.*;

// This file provides RAC implementations for \\string functionality
// Though \string is defined for arbitrary character sequences, this implementation only allows lengths up to Integer.MAX_VALUE

public final class string implements IJmlPrimitiveType, IJmlIntArrayLike, Comparable<string> {

    private String value = "";
    
    private string(String s) {
        value = s;
    }
    
    public static string empty() {
        return new string("");
    }
    
    public boolean isEmpty() {
        return value.isEmpty();
    }
    
    // FIXME - which to use size or length?
    public bigint length() {
        return bigint.of(value.length());
    }
    
    public bigint size() {
        return bigint.of(value.length());
    }
    
    public String toString() {
        return value;
    }
    
    public static string of(String s) {
        return new string(s);
    }
    
    /** Unchecked getChar -- out of range values are 'undefined' */
    private char _get(bigint i) {
        if (indexOK(i)) return value.charAt(i.intValue());
        return (char)0;
    }
    
    public char get(bigint i) {
        if (indexOK(i)) return value.charAt(i.intValue());
        throw exc(i, "get");
    }
    
    // FIXME - remove
    public static boolean eq(string s, string ss) {
        return s.value.equals(ss.value);
    }
    
    public int compareTo(string s) {
        return value.compareTo(s.value);
    }
 
    public boolean eq(string s) {
        return this.value.equals(s.value);
    }
    
    public boolean ne(string s) {
        return !eq(s);
    }
    
    public boolean ge(string s) {
        return compareTo(s) >= 0;
    }
    
    public boolean gt(string s) {
        return compareTo(s) > 0;
    }
    
    public boolean le(string s) {
        return compareTo(s) <= 0;
    }
    
    public boolean lt(string s) {
        return compareTo(s) < 0;
    }
    
    public char head() {
        return value.charAt(0);
    }
    
    public string tail() {
        return new string(value.substring(1));
    }
    
    public string add(char v) {
        return new string(value.concat(String.valueOf(v)));
    }

    public static string concat(string s, string ss) {
        return new string(s.value + ss.value);
    }
 
    public string append(string s) {
        return concat(this,s);
    }

    public string put(bigint ii, char v) {
        if (indexOK(ii)) throw exc(ii, "put");
        int i = ii.intValue();
        return new string(value.substring(0,i) + v + value.substring(i+1));
    }
    
    public string insert(bigint ii, char v) {
        int i = ii.intValue();
        return new string(value.substring(0,i) + v + value.substring(i));
    }

    public string remove(bigint ii) {
        int i = ii.intValue();
        return new string(value.substring(0,i) + value.substring(i+1));
    }

    public string substring(bigint start, bigint end) {
        return new string(value.substring(start.intValue(), end.intValue()));
    }
    
    public boolean equals(Object o) { throw new UnsupportedOperationException(); }
    public int hashCode() { return value.hashCode(); }
    
    private boolean indexOK(bigint i) {
        return i.ge(bigint.of(0)) && i.lt(bigint.of(value.length()));
    }
    private RuntimeException exc(bigint i, String method) {
        return new StringIndexOutOfBoundsException("index " + i.intValue() + " is not in 0 .. " + (value.length()-1) + " in call of " + method);
    }
}
