package org.jmlspecs.lang;

import org.jmlspecs.utils.Utils;

public class JML {
    // Note that there is a JML.jml file; it contains all of the specifications
    // for the following methods and additional model methods. It needs to be
    // in a .jml file because at runtime this .java file is only available in
    // compiled form, in the runtime library. That also means that if these
    // methods are used for ESC or RAC, the system Specs files (where JML.jml
    // lives) must be on the specs path.

    public /*@ pure */ static <T> T lbl(String id, T expr) { // Works for primitive types by autoboxing
        Utils.reportObject(id, expr);
        return expr;
    }
    
    public /*@ pure */ static boolean lbl(String id, boolean expr) { // Avoids autoboxing
        Utils.reportBoolean(id, expr);
        return expr;
    }
    
    public /*@ pure */ static int lbl(String id, int expr) { // Avoids autoboxing
        Utils.reportInt(id, expr);
        return expr;
    }
    
    public /*@ pure */ static long lbl(String id, long expr) { // Avoids autoboxing
        Utils.reportLong(id, expr);
        return expr;
    }
    
    public /*@ pure */ static short lbl(String id, short expr) { // Avoids autoboxing
        Utils.reportShort(id, expr);
        return expr;
    }
    
    public /*@ pure */ static byte lbl(String id, byte expr) { // Avoids autoboxing
        Utils.reportByte(id, expr);
        return expr;
    }
    
    public /*@ pure */ static char lbl(String id, char expr) { // Avoids autoboxing
        Utils.reportChar(id, expr);
        return expr;
    }
    
    public /*@ pure */ static float lbl(String id, float expr) { // Avoids autoboxing
        Utils.reportFloat(id, expr);
        return expr;
    }
    
    public /*@ pure */ static double lbl(String id, double expr) { // Avoids autoboxing
        Utils.reportDouble(id, expr);
        return expr;
    }
    
    public /*@ pure */ static boolean lblpos(String id, boolean expr) {
        if (expr) Utils.reportBoolean(id, expr);
        return expr;
    }
    
    public /*@ pure */ static boolean lblneg(String id, boolean expr) {
        if (!expr) Utils.reportBoolean(id, expr);
        return expr;
    }
    
    public static boolean informal(String s) {
        return true;
    }
}
