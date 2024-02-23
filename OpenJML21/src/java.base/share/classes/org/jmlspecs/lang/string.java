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

    public static string empty() {
        return new string("");
    }

    public boolean isEmpty() {
        return racValue.isEmpty();
    }
    
    public static boolean equals(string s, string ss) {
        return s.racValue.equals(ss.racValue);
    }
 
    public boolean equals(string s) {
        return this.racValue.equals(s.racValue);
    }
    
    public string add(char v) {
        return new string(racValue.concat(String.valueOf(v)));
    }

    
    

}
