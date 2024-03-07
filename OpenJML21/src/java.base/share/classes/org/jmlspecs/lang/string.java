package org.jmlspecs.lang;

// All the specifications are in the .jml file. 
// This file provides RAC implementations

//@ immutable pure
public final class string implements IJmlPrimitiveType, IJmlIntArrayLike {

    public String racValue = "";
    
    private string(String s) {
        racValue = s;
    }
    
    static public string string(String s) {
        return new string(s);
    }
    
    public char get(int i) { // FIXME - change to bigint eventually
        if (i < 0 || i >= racValue.length()) return (char)0;
        return racValue.charAt(i);
    }
    
    public string put(int i, char v) {
        return string(racValue.substring(0,i) + v + racValue.substring(i+1));
    }
    
    static public string of(String s) {
        return string(s);
    }

    public static string empty() {
        return string("");
    }
    
    public long size() {  // FIXME - change to bigint eventuallu
        return (long)(racValue.length());
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
    
    public static boolean equals(Object o, Object oo) { throw new UnsupportedOperationException(); }
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

    public string insert(int i, char v) {
        return string(racValue.substring(0,i) + v + racValue.substring(i));
    }

    public string remove(int i) {
        return string(racValue.substring(0,i) + racValue.substring(i+1));
    }

    public string substring(int start, int end) {
        return string(racValue.substring(start, end));
    }

    
    

}
