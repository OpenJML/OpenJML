package org.jmlspecs.lang;

import org.jmlspecs.utils.Utils;

public class JML {
    // Note that there is a JML.jml file; it contains all of the specifications
    // for the following methods and additional model methods. It needs to be
    // in a .jml file because at runtime this .java file is only available in
    // compiled form, in the runtime library. That also means that if these
    // methods are used for ESC or RAC, the system Specs files (where JML.jml
    // lives) must be on the specs path.

    public static <T> T lbl(String id, T expr) { // Works for primitive types by autoboxing
        Utils.reportObject(id, expr);
        return expr;
    }
    
    public static boolean lbl(String id, boolean expr) { // Avoids autoboxing
        Utils.reportBoolean(id, expr);
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
    
    public static boolean informal(String s) {
        return true;
    }
}
