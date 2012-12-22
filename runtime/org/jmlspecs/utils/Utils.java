package org.jmlspecs.utils;

import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;
import org.jmlspecs.annotation.*; // Keep this to match the .jml file, for now

/** 
 * This class contains utility methods used in internal translations for both
 * ESC and RAC.  In RAC, these functions are executed to provide the built-in
 * functionality; in ESC, the specifications written here are used to provide
 * background predicate logic for built-in functionality. 
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
    
    static final public String invariantMethodString = "_JML$$$checkInvariant";
    static final public String staticinvariantMethodString = "_JML$$$checkStaticInvariant";

    /** Reports aJML assertion (any JML precondition, postcondition, etc.)
     * failure with the given message.
     * @param message The message to report
     */
    public static void assertionFailure(String message) {
        if (useExceptions) throw new JmlAssertionError(message);
        //if (useJavaAssert) assert false: message;
        System.out.println(message); System.out.flush();
        if (showStack) (new JmlAssertionError(message)).printStackTrace(System.out);
    }
    
    /** Reports aJML assertion failure with the given message if the second argument is null
     * @param message the message to report if the second argument is null
     * @param v value to be tested 
     * @return the object which is the last argument
     */
    //@ ensures \result == v;
    public static <T> T nonNullCheck(String message, T v) {
        if (v == null) assertionFailure(message);
        return v;
    }
    
    /** Reports aJML assertion failure with the given message if the second argument is false
     * @param message the message to report if the second argument is false
     * @param b value to be tested 
     * @param v value to be returned 
     * @return the object which is the last argument
     */
    public static <T> T trueCheck(String message, boolean b, T v) {
        if (!b) assertionFailure(message);
        return v;
    }
    
    /** Reports a JML assertion failure with the given message if the second argument 
     * is not equal to the third (this is a test for object non-equality)
     * @param message the message to report if the second argument and third arguments are not equal
     * @param o value to be tested 
     * @param v value to be returned 
     * @return the object which is the last argument
     */
    public static <T> T eqCheck(String message, Object o, T v) {
        if (o != v) assertionFailure(message);
        return v;
    }
    
    // TODO - document
    public static int intRangeCheck(String message, int low, int high, int v) {
        if (low <= v && v <= high) assertionFailure(message);
        return v;
    }
    
    // TODO - document
    public static int zeroIntCheck(String message, int v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    // TODO - document
    public static long zeroLongCheck(String message, long v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    // TODO - document
    public static double zeroDoubleCheck(String message, double v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    // TODO - document
    public static float zeroFloatCheck(String message, float v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    // TODO - document
    public static short zeroShortCheck(String message, short v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    // TODO - document
    public static byte zeroByteCheck(String message, byte v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    // TODO - document
    public static char zeroCharCheck(String message, char v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    /** Reports aJML assertion failure with optional additional information
     * @param message the message to report
     * @param optMessage possibly null additional information
     */
    public static void assertionFailure2(String message, /*@ nullable*/ String optMessage) {
        if (optMessage != null) message = message + " (" + optMessage + ")";
        assertionFailure(message);
    }
    
    /** Tests that an array and all the elements of the array are non-null 
     * @param array the array to test
     * @return true if all elements are not null, false if at least one is
     */  // FIXME - this is a different style from the others - it emits no message
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
    public static class JmlAssertionError extends java.lang.Error {
        //private static final long serialVersionUID = 1L;
        /** The constructor with an informational message string
         * @param s the reason for the failure
         */
        public JmlAssertionError(String s) {
            super(s);
        }
    }
    
    // The remaining declarations provide a mechanism for reporting
    // values encountered during execution.

    /** Reports a byte value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static byte reportByte(String key, byte v) {
        System.out.println("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a short value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static short reportShort(String key, short v) {
        System.out.println("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a char value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static char reportChar(String key, char v) {
        System.out.println("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a long value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static long reportLong(String key, long v) {
        System.out.println("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a float value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static float reportFloat(String key, float v) {
        System.out.println("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a double value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static double reportDouble(String key, double v) {
        System.out.println("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a boolean value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static boolean reportBoolean(String key, boolean v) {
        System.out.println("LABEL " + key + " = " + v);System.out.flush();
        return v;
    }

    /** Reports a int value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static int reportInt(String key, int v) {
        System.out.println("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a Object value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static Object reportObject(String key, Object v) {
        System.out.println("LABEL " + key + " = " + v);
        return v;
    }


    static public void callClassInvariant(Object o, String fqClassName) {
        String ms = "???";
        try {
            Class<?> clazz = Class.forName(fqClassName);
            ms = invariantMethodString + "$$" + fqClassName.replace(".","$");
            Method m = clazz.getMethod(ms);
            m.invoke(o);
        } catch (Exception e) {
            // If no class or method found, we ignore
            //System.out.println("FAILED TO CALL INVARIANT FOR " + ms + " " + e.getMessage());
            //e.printStackTrace(System.out);
        }
    }
    
    static public void callStaticClassInvariant(String fqClassName) {
        try {
            Class<?> clazz = Class.forName(fqClassName);
            Method m = clazz.getMethod(staticinvariantMethodString);
            m.invoke(null);
        } catch (Exception e) {
            //System.out.println("FAILED TO CALL STATIC INVARIANT FOR " + fqClassName);
            //e.printStackTrace(System.out);
            // If no class or method found, we ignore
        }
    }
    
//    /** Deletes all values from the database */
//    public static void clearValues() {
//        map = new HashMap<String,Object>();
//    }
//    
//    /** Prints all values in the database and then deletes them */
//    public static void printValues() {
////        java.util.Iterator<Map.Entry<String,Object>> i = map.entrySet().iterator();
////        for ( ; i.hasNext(); ) {
////            Map.Entry<String,Object> e = i.next();
////            System.out.println("LABEL " + e.getKey() + " = " + e.getValue());
////        }
//        // It turns out that with system-compiled RAC files, printValues() can get
//        // called before System.out is initialized (scary)
//        // FIXME - perhaps we do not need printValues any more since we are printing values as they happen
//        if (System.out!=null) System.out.flush();
//        clearValues();
//    }
//    public static void printValues() {
//        for (Map.Entry<String,Object> e : map.entrySet()) {
//            System.out.println("LABEL " + e.getKey() + " = " + e.getValue());
//        }
//        clearValues();
//    }

    // TODO - document - this and following
    public static  IJMLTYPE makeTYPE(Class<?> base, IJMLTYPE... args) {
        return JmlTypeRac.make(base,args);
    }
    
    public static final IJMLTYPE[] emptyArgs = {};
    
    public static  IJMLTYPE makeTYPE0(Class<?> base) {
        if (base == null) return null;
        return JmlTypeRac.make(base,emptyArgs);
    }
    
    public static  IJMLTYPE makeTYPE1(Class<?> base, IJMLTYPE a0) {
        if (base == null) return null;
        return JmlTypeRac.make(base,new IJMLTYPE[]{a0});
    }
    
    public static  IJMLTYPE makeTYPE2(Class<?> base, IJMLTYPE a0, IJMLTYPE a1) {
        if (base == null) return null;
        return JmlTypeRac.make(base,new IJMLTYPE[]{a0,a1});
    }
    
    public static  Class<?> erasure(IJMLTYPE t) {
        return t.erasure();
    }
    
    public static boolean isSubTypeOf(IJMLTYPE t, IJMLTYPE tt) {
        try {
            return tt.erasure().isAssignableFrom(t.erasure());
        } catch (java.lang.IncompatibleClassChangeError e) {
            System.err.println("ISTO: " + t.erasure() + " " + tt.erasure());
            return false;
        }
    }
    
    // TODO - document this and following
    private static class JmlTypeRac implements IJMLTYPE {

        final private Class<?> base;
        final private IJMLTYPE[] args;
        final private static Map<IJMLTYPE,IJMLTYPE> internSet = new HashMap<IJMLTYPE,IJMLTYPE>();
        
        public static IJMLTYPE make(Class<?> base, IJMLTYPE... args) {
            JmlTypeRac t = new JmlTypeRac(base,args);
            return t.intern();
        }
        
        public String toString() {
            String s = base.toString();
            if (args != null && args.length > 0) {
                s = s + "<";
                boolean first = true;
                for (IJMLTYPE t: args) {
                    if (first) first = false; else s = s + ",";
                    s = s + t.toString();
                }
                s = s + ">";
            }
            return s;
        }
        
        private IJMLTYPE intern() {
            IJMLTYPE tt = internSet.get(this);
            if (tt == null) {
                tt = this;
                internSet.put(this,this);
            }
            return tt;
        }
        
        private JmlTypeRac(Class<?> base, IJMLTYPE... args) {
            this.base = base;
            this.args = args;
        }

        @Override
        public IJMLTYPE arg(int i) {
            return args[i];
        }

        @Override
        public boolean equals(IJMLTYPE t) {
            if (t == null) return false;
            if (this == t) return true;
            if (!(t instanceof JmlTypeRac)) return false;
            JmlTypeRac tt = (JmlTypeRac)t;
            if (erasure() != tt.erasure()) return false;
            if (args.length != tt.args.length) return false;
            for (int i=0; i<args.length; i++) {
                if (!args[i].equals(tt.args[i])) return false;
            }
            return true;
        }
        
        //JAVA16  @Override
        public int hashCode() {
            int i = base.hashCode();
            int k = 0;
            for (IJMLTYPE t: args) i = i + (t.hashCode()<< (++k));
            return i;
        }

        @Override
        public Class<?> erasure() {
            return base;
        }

        @Override
        public boolean isArray() {
            return base.isArray();
        }

        @Override
        public boolean isSubtypeOf(IJMLTYPE t) {
            return t.erasure().isAssignableFrom(this.base);
        }

        @Override
        public int numargs() {
            // TODO Auto-generated method stub
            return 0;
        }
    }
    
    public static interface ValueBool {
        public boolean value(final Object[] args);
     }

    public static interface ValueInt {
        public int value(final Object[] args);
     }

    public static interface ValueShort {
        public short value(final Object[] args);
     }

    public static interface ValueChar {
        public char value(final Object[] args);
     }

    public static interface ValueLong {
        public long value(final Object[] args);
     }

    public static interface ValueByte {
        public byte value(final Object[] args);
     }

    public static interface ValueFloat {
        public float value(final Object[] args);
     }

    public static interface ValueDouble {
        public double value(final Object[] args);
     }

    public static interface Value<T> {
        public T value(final Object[] args);
     }

}
