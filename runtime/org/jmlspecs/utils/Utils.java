package org.jmlspecs.utils;

import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;

import com.sun.tools.javac.comp.JmlRac;

/** 
 * This class contains utility methods used during runtime assertion
 * checking.
 * @author David Cok
 *
 */
public class Utils {
    
    //@ public normal_behavior
    //@    ensures \result.size() == 0;
    static public /*@non_null pure */ <E> org.jmlspecs.lang.JMLList<E> defaultEmpty() {
        return null;
    }
    
    /** Determines whether to report assertion failures as exceptions (true)
     * or error messages (false).
     */
    public static boolean useExceptions = System.getProperty("org.jmlspecs.openjml.racexceptions") != null;
    
    /** If true, then error messages reporting assertion failures are 
     * accompanied with a stack trace to log.errorWriter.
     */
    public static boolean showStack = System.getProperty("org.jmlspecs.openjml.racshowstack") != null;
    
    /** Reports a JML assertion (any JML precondition, postcondition, etc.)
     * failure with the given message.
     * @param message The message to report
     */
    public static void assertionFailure(String message) {
        if (useExceptions) throw new JmlAssertionFailure(message);
        System.out.println(message);
        if (showStack) (new JmlAssertionFailure(message)).printStackTrace(System.out);
    }
    
    /** Reports a JML assertion failure with the given message if the second argument is null
     * @param message the message to report if the second argument is null
     * @param v value to be tested 
     * @return the object which is the second argument
     */
    public static <T> T nonNullCheck(String message, T v) {
        if (v == null) assertionFailure(message);
        return v;
    }
    
    public static <T> T trueCheck(String message, boolean b, T v) {
        if (!b) assertionFailure(message);
        return v;
    }
    
    public static <T> T eqCheck(String message, Object o, T v) {
        if (o != v) assertionFailure(message);
        return v;
    }
    
    public static int intRangeCheck(String message, int low, int high, int v) {
        if (low <= v && v <= high) assertionFailure(message);
        return v;
    }
    
    public static int zeroIntCheck(String message, int v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    /** Reports a JML assertion failure with optional additional information
     * @param message the message to report
     * @param optMessage possibly null additional information
     */
    public static void assertionFailure2(String message, /*@ nullable*/ String optMessage) {
        if (optMessage != null) message = message + " (" + optMessage + ")";
        assertionFailure(message);
    }
    
    /** Tests that all the elements of the array are non-null 
     * @param array the array to test
     * @return true if all elements are not null, false if at least one is
     */
    public static boolean nonnullElementCheck(Object[] array) {
        if (array == null) return false;
        for (Object o: array) {
            if (o == null) return false;
        }
        return true;
    }
    
//    public final static Class<?>[] noParams = {};
//    public final static Object[] noArgs = {};
//    
//    public static Method callSuperInvariantCheck(Object o) {
//        try {
//            Class<?> cl = o.getClass();
//            System.out.println("CALLED WITH " + cl);
//            while (true) {
//                cl = cl.getSuperclass();
//                System.out.println("SUPER IS " + cl);
//                if (cl == null) return null;
//                Method m = cl.getMethod("_JML$$$checkInvariant",noParams);
//                System.out.println("METHOD IS " + m);
//                return m;
//                //if (m != null) { m.invoke(o,noArgs); return; }
//            }
//        } catch (Exception e) {
//            // If getMethod does not find a method we end here
//            // If invoke fails we end here
//            System.out.println(e);
//        }
//        return null;
//    }
    
    /** Error object that is thrown when any JML assertion failure is 
     * encountered (if exceptions are enabled using Utils.useExceptions)
     * @author David Cok
     */
    public static class JmlAssertionFailure extends java.lang.Error {
        //private static final long serialVersionUID = 1L;
        /** The constructor with an informational message string
         * @param s the reason for the failure
         */
        public JmlAssertionFailure(String s) {
            super(s);
        }
    }
    
    // The remaining declarations provide a mechanism for saving and reporting
    // values encountered during execution.
    
    /** The map for storing runtime values */
    static HashMap<String,Object> map = new HashMap<String,Object>();
    
    /** Saves a byte value under the given key
     * @param key the name under which to store the value
     * @param v the value to store
     * @return the value of v
     */
    public static byte saveByte(String key, byte v) {
        map.put(key,v);
        return v;
    }
    
    /** Saves a short value under the given key
     * @param key the name under which to store the value
     * @param v the value to store
     * @return the value of v
     */
    public static short saveShort(String key, short v) {
        map.put(key,v);
        return v;
    }
    
    /** Saves a char value under the given key
     * @param key the name under which to store the value
     * @param v the value to store
     * @return the value of v
     */
    public static char saveChar(String key, char v) {
        map.put(key,v);
        return v;
    }
    
    /** Saves a long value under the given key
     * @param key the name under which to store the value
     * @param v the value to store
     * @return the value of v
     */
    public static long saveLong(String key, long v) {
        map.put(key,v);
        return v;
    }
    
    /** Saves a float value under the given key
     * @param key the name under which to store the value
     * @param v the value to store
     * @return the value of v
     */
    public static float saveFloat(String key, float v) {
        map.put(key,v);
        return v;
    }
    
    /** Saves a double value under the given key
     * @param key the name under which to store the value
     * @param v the value to store
     * @return the value of v
     */
    public static double saveDouble(String key, double v) {
        map.put(key,v);
        return v;
    }
    
    /** Saves a boolean value under the given key
     * @param key the name under which to store the value
     * @param v the value to store
     * @return the value of v
     */
    public static boolean saveBoolean(String key, boolean v) {
        map.put(key,v);
        return v;
    }
    
    /** Saves a int value under the given key
     * @param key the name under which to store the value
     * @param v the value to store
     * @return the value of v
     */
    public static int saveInt(String key, int v) {
        map.put(key,v);
        return v;
    }
    
    /** Saves a Object value under the given key
     * @param key the name under which to store the value
     * @param v the value to store
     * @return the value of v
     */
    public static Object saveObject(String key, Object v) {
        map.put(key,v);
        return v;
    }
    
    static public void callClassInvariant(Object o, String fqClassName) {
        try {
            Class<?> clazz = Class.forName(fqClassName);
            Method m = clazz.getMethod(JmlRac.invariantMethodString);
            m.invoke(o);
        } catch (Exception e) {
            // If no class or method found, we ignore
            //System.out.println("FAILED TO CALL INVARIANT FOR " + fqClassName);
            //e.printStackTrace(System.out);
        }
    }
    
    static public void callStaticClassInvariant(String fqClassName) {
        try {
            Class<?> clazz = Class.forName(fqClassName);
            Method m = clazz.getMethod(JmlRac.staticinvariantMethodString);
            m.invoke(null);
        } catch (Exception e) {
            //System.out.println("FAILED TO CALL STATIC INVARIANT FOR " + fqClassName);
            //e.printStackTrace(System.out);
            // If no class or method found, we ignore
        }
    }
    
    /** Deletes all values from the database */
    public static void clearValues() {
        map = new HashMap<String,Object>();
    }
    
    /** Prints all values in the database and then deletes them */
    public static void printValues() {
        java.util.Iterator<Map.Entry<String,Object>> i = map.entrySet().iterator();
        for ( ; i.hasNext(); ) {
            Map.Entry<String,Object> e = i.next();
            System.out.println("LABEL " + e.getKey() + " = " + e.getValue());
        }
        clearValues();
    }
//    public static void printValues() {
//        for (Map.Entry<String,Object> e : map.entrySet()) {
//            System.out.println("LABEL " + e.getKey() + " = " + e.getValue());
//        }
//        clearValues();
//    }
}
