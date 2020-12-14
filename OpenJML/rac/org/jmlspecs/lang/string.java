package org.jmlspecs.lang;

//@ immutable pure non_null_by_default
public class string implements IJmlPrimitiveType, IJmlIntArrayLike {

    public String racValue;
    
    private string(/*@ non_null*/String s) {
        racValue = s;
    }
    
//    static public string string(/*@ non_null */ String s) {
//        return new string(s);
//    }

    public static string empty() {
        return new string("");
    }

    public boolean isEmpty() {
        return racValue.isEmpty();
    }
    

  

}
