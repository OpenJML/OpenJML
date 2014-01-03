package org.jmlspecs.lang;

import org.jmlspecs.utils.Utils;

public class JML {
    // Note that there is a JML.jml file; it contains all of the specifications
    // for the following methods and additional model methods.

    public static <T> T lbl(String id, T expr) {
        Utils.reportObject(id, expr);
        return expr;
    }
    
    public static int lbl(String id, int expr) { // FIXME - needs other primtive types
        Utils.reportInt(id, expr);
        return expr;
    }
    
    public static boolean lblpos(String id, boolean expr) {
        if (expr) Utils.reportBoolean(id, expr);
        return expr;
    }
    
    public static boolean lblneg(String id, boolean expr) {
        if (!expr) Utils.reportBoolean(id, expr);
        return expr;
    }
    

    //@ public normal_behavior
    //@ ensures \result;
    //@ pure helper
    public static boolean informal(String s) {
        return true;
    }
}
