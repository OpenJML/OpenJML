package org.jmlspecs.lang.internal;

import org.jmlspecs.lang.IJmlIntArrayLike;
import org.jmlspecs.lang.IJmlPrimitiveType;

// This file provides RAC implementations for \\string functionality
// Though \string is defined for arbitrary character sequences, this implementation only allows lengths up to Integer.MAX_VALUE

public final class string implements IJmlPrimitiveType, IJmlIntArrayLike, Comparable<string> {

    private final String value;
    
    private final static String emptyString = "";

    public final static string empty = of(emptyString);
    
    private string(String s) {
        value = s;
    }
    
    public static string empty() {
        return new string(emptyString);
    }
    
    public boolean isEmpty() {
        return value.isEmpty();
    }
    
    public bigint length() {
        return bigint.of(value.length());
    }
    
    public String toString() {
        return value;
    }
    
    public static string of(String s) {
        return new string(s);
    }
    
    public static string of(char c) {
        return new string(String.valueOf(c));
    }
    
    public char get(bigint i) {
        if (indexOK(i)) return value.charAt(i.intValue());
        throw exc(i, "get");
    }
    
    public char getUnchecked(bigint i) {
        if (indexOK(i)) return value.charAt(i.intValue());
        return 0;
    }
    
    // Expects but does not check that all indices are in range.
    public static boolean eqspan(string a, bigint astart, string b, bigint bstart, bigint len) {
        for (bigint i = bigint.zero; i.lt(len); i = i.add(bigint.one)) {
            if (a.value.charAt(astart.add(i).intValue()) != b.value.charAt(bstart.add(i).intValue())) return false;
        }
        return true;
    }
    
    public int compareTo(string s) {
        return value.compareTo(s.value);
    }
 
    public boolean eq(string s) {
        if (this.value.length() != s.value.length()) return false;
        return eqspan(this, bigint.zero, s, bigint.zero, s.length());
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
    
    public string head(bigint k) {
        return new string(value.substring(0,k.intValue()));
    }
    
    public string tail() {
        return new string(value.substring(1));
    }
    
    public string tail(bigint k) {
        return new string(value.substring(k.intValue()));
    }
    
    public string prepend(char v) {
        return string.of(v).append(this);
    }
    
    public string append(char v) {
        return this.append(string.of(v));
    }

    public string append(String s) {
        return this.append(string.of(s));
    }

    public string append(string s) {
        return new string(this.value + s.value);
    }

    public string put(bigint ii, char v) {
        if (!indexOK(ii)) throw exc(ii, "put");
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

    public boolean startsWith(string prefix) {
        if (prefix.length().gt(this.length())) return false;
        return eqspan(this, bigint.zero, prefix, bigint.zero, prefix.length());
    }
    
    public boolean endsWith(string suffix) {
        if (suffix.length().gt(this.length())) return false;
        return eqspan(this, this.length().subtract(suffix.length()), suffix, bigint.zero, suffix.length());
    }
    
    public string substring(bigint start, bigint end) {
        if (start.lt(bigint.zero) || end.lt(start) || length().lt(end)) throw new StringIndexOutOfBoundsException("\\string.substring: out of range indices: " + start + " " + end + " " + length());
        return new string(value.substring(start.intValue(), end.intValue()));
    }
    
    public boolean equals(string s) { return value.equals(s.value); }
    public boolean equals(Object o) { return o instanceof string s ? equals(s) : (o instanceof String st && this.value.equals(st)) ; }

    public int hashCode() { return value.hashCode(); }
    
    private boolean indexOK(bigint i) {
        return i.ge(bigint.of(0)) && i.lt(bigint.of(value.length()));
    }
    private boolean indexOK(int i) { // Conversions to bigint do not happen in pure Java
        return i >= 0 && i < value.length();
    }
    private RuntimeException exc(bigint i, String method) {
        return new StringIndexOutOfBoundsException("index " + i + " is not in 0 .. " + (value.length()-1) + " in call of " + method);
    }
}
