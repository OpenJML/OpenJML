package org.jmlspecs.lang;


public class JML {
    // Note that there is a JML.jml file; it contains all of the specifications
    // for the following methods and additional model methods. It needs to be
    // in a .jml file because at runtime this .java file is only available in
    // compiled form, in the runtime library. That also means that if these
    // methods are used for ESC or RAC, the system Specs files (where JML.jml
    // lives) must be on the specs path.

    //@ model public /*@ pure */ static <T> T lbl(String id, T expr);
    
	//@ model public /*@ pure */ static boolean lbl(String id, boolean expr);
    
	//@ model public /*@ pure */ static int lbl(String id, int expr);
    
	//@ model public /*@ pure */ static long lbl(String id, long expr);
    
	//@ model public /*@ pure */ static short lbl(String id, short expr);
    
	//@ model public /*@ pure */ static byte lbl(String id, byte expr);
    
	//@ model public /*@ pure */ static char lbl(String id, char expr);
    
	//@ model public /*@ pure */ static float lbl(String id, float expr);
    
	//@ model public /*@ pure */ static double lbl(String id, double expr);
    
	//@ model public /*@ pure */ static boolean lblpos(String id, boolean expr);
    
	//@ model public /*@ pure */ static boolean lblneg(String id, boolean expr);
    
	//@ model public static boolean informal(String s);
}
