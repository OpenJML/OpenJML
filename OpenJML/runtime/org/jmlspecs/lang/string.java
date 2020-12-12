package org.jmlspecs.lang;

//@ immutable pure
public class string implements IJmlPrimitiveType, IJmlIntArrayLike {
    //@ non_null 
    public String racValue;
    
    private string(/*@ non_null*/String s) {
        racValue = s;
        //@ set length = s.length();
    }
    
    static public string string(/*@ non_null */ String s) {
        return new string(s);
    }

    public static string empty() {
        return new string("");
    }

    public boolean isEmpty() {
        return racValue.isEmpty();
    }
    
    //@ model public \bigint size() { return racValue.length(); }

  

}
