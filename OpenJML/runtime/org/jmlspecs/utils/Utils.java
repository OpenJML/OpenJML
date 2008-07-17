package org.jmlspecs.utils;


import java.util.HashMap;
import java.util.Map;


public class Utils {
    
    /** Determines whether to report assertion failures as exceptions (true)
     * or error messages (false).
     */
    public static boolean useExceptions = false;
    
    /** If true, then error messages reporting assertion failures are 
     * accompanied with a stack trace to System.out.
     */
    public static boolean showStack = false;
    
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
    public static Object nonNullCheck(String message, Object v) {
        if (v == null) assertionFailure(message);
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
        private static final long serialVersionUID = 1L;
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
    
    /** Deletes all values from the database */
    public static void clearValues() {
        map = new HashMap<String,Object>();
    }
    
    /** Prints all values in the database and then deletes them */
    public static void printValues() {
        for (Map.Entry<String,Object> e : map.entrySet()) {
            System.out.println("LABEL " + e.getKey() + " = " + e.getValue());
        }
        clearValues();
    }
    
}
