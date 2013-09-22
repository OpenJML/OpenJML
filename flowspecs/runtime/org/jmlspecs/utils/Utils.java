/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */

package org.jmlspecs.utils;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import org.jmlspecs.lang.Real;




/** 
 * This class contains utility methods used in internal translations for both
 * ESC and RAC.  In RAC, these functions are executed to provide the built-in
 * functionality; in ESC, the specifications written here are used to provide
 * background predicate logic for built-in functionality. 
 * @author David Cok
 */
public class Utils {
    /** Reports a JML assertion (any JML precondition, postcondition, etc.)
     * failure with the given message.
     * @param message The message to report
     */
    // This one is declared first to minimize changes to its location 
    public static final String ASSERTION_FAILURE = "assertionFailureL"; // Must match the method name
    public static void assertionFailureL(String message, /*@ nullable */String label) {
        if (useExceptions) {
            String exname = System.getProperty("org.openjml.exception."+label);
            if (exname == null) {
                exname = "org.jmlspecs.utils.JmlAssertionError" + "." + label;
            }
            Class<?> c;
            try { c = Class.forName(exname); } catch (ClassNotFoundException e) { c = null; }
            if (c != null) {
                try {
                    Constructor<? extends Error> cc = ((Class<? extends Error>)c).getConstructor(String.class,String.class);
                    Error e = cc.newInstance(message,label);
                    throw e;
                } catch (NoSuchMethodException e) {
                    throw new JmlAssertionError(message,label);
                } catch (InstantiationException e) {
                    throw new JmlAssertionError(message,label);
                } catch (InvocationTargetException e) {
                    throw new JmlAssertionError(message,label);
                } catch (IllegalAccessException e) {
                    throw new JmlAssertionError(message,label);
                }
            }
            if ("Precondition".equals(label)) throw new JmlAssertionError.Precondition(message,label); else throw new JmlAssertionError(message,label);}
        else if (useJavaAssert) assert false: message;
        else { System.out.println(message); System.out.flush();
            if (showStack) { Error e = ("Precondition".equals(label)) ? new JmlAssertionError.Precondition(message,label): new JmlAssertionError(message,label);
                e.printStackTrace(System.out); // Keep the new expressions on line 27 or some test results will change
            }
        }
    }
    
    // Deprecate this
    public static void assertionFailure(String message) {
        assertionFailureL(message,null);
    }
    
    //@ public normal_behavior
    //@    ensures \result.size() == 0;
    static public /*@non_null pure */ <E> org.jmlspecs.lang.JMLList<E> defaultEmpty() {
        return null;
    }
    
    /** Determines whether to report assertion failures as exceptions (true)
     * or error messages (false).
     */
    public static boolean useExceptions = System.getProperty("org.jmlspecs.openjml.racexceptions") != null;
    
    /** Determines whether to report assertion failures as exceptions (true)
     * or error messages (false).
     */
    public static boolean useJavaAssert = System.getProperty("org.jmlspecs.openjml.racjavaassert") != null;
    
//    public static boolean showRacSource;
//    static {
//        String s = System.getProperty("org.openjml.rac.showRacSource");
//        showRacSource = s != null && !s.equals("false");
//    }
    
    /** If true, then error messages reporting assertion failures are 
     * accompanied with a stack trace to log.errorWriter.
     */
    public static boolean showStack = System.getProperty("org.jmlspecs.openjml.racshowstack") != null;
    
    static final public String invariantMethodString = "_JML$$$checkInvariant";
    static final public String staticinvariantMethodString = "_JML$$$checkStaticInvariant";

    /** Reports a JML assertion failure with the given message if the second argument is null
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
    
    public static String typeName(Throwable t) {
        return t.getClass().toString();
    }
    
    /** Reports a JML assertion failure with optional additional information
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
    
    // The report... methods provide a mechanism for reporting
    // values encountered during execution.
    
    /** Just prints out a message */
    public static void report(String str) {
        System.out.println(str);
    }
    
    public static final String REPORT_EXCEPTION = "reportException"; // must match method name
    /** Prints out a message, the exception message, and the exception stack */
    public static void reportException(String str, RuntimeException e) {
        System.out.println(str);
        e.printStackTrace(System.out);
    }

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
    
    public static  IJMLTYPE makeTYPEN(Class<?> base) {
        return JmlTypeRac.make(base,null);
    }
    
    public static  IJMLTYPE makeTYPEQ() {
        return JmlTypeRac.make(null,null);
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
    
    public static IJMLTYPE getComponentType(IJMLTYPE t) {
        return makeTYPE0(t.erasure().getComponentType());
    }
    
    
    public static String getClassName(Object o) {
        return o.getClass().getName();
    }
    
    public static String concat(String s1, String s2) {
        return s1 + s2;
    }
    
    public static boolean isSubTypeOf(IJMLTYPE t, IJMLTYPE tt) {
        try {
            return tt.erasure().isAssignableFrom(t.erasure());
        } catch (java.lang.IncompatibleClassChangeError e) {
            System.err.println("ISTO: " + t.erasure() + " " + tt.erasure());
            return false;
        }
    }
    
    public static boolean isEqualTo(IJMLTYPE t, IJMLTYPE tt) {
        if (t == tt) return true;
        if (t == null || tt == null) return false;
        return tt.erasure() == t.erasure();
//        JmlTypeRac tt = (JmlTypeRac)t;
//        if (erasure() != tt.erasure()) return false;
//        if (args.length != tt.args.length) return false;
//        for (int i=0; i<args.length; i++) {
//            if (!args[i].equals(tt.args[i])) return false;
//        }
//        return true;
    }
    
    public static <T> Iterator<T> iterator(Iterable<T> iterable) {
        return iterable.iterator();
    }
    
    public static <T> T next(Iterator<T> iterable) {
        return iterable.next();
    }
    
    public static boolean hasNext(Iterator<?> iterable) {
        return iterable.hasNext();
    }
    
    // TODO - document this and following
    private static class JmlTypeRac implements IJMLTYPE {

        final private Class<?> base;
        final private IJMLTYPE[] args;
        final private static Map<IJMLTYPE,IJMLTYPE> internSet = new HashMap<IJMLTYPE,IJMLTYPE>();
        
        public static IJMLTYPE make(Class<?> base, IJMLTYPE[] args) {
            JmlTypeRac t = new JmlTypeRac(base,args);
            return t.intern();
        }
        
        public String toString() {
            if (base == null) return "?"; // FIXME - really this is just unknown, not a wildcard
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
            return isEqualTo(this,t);
        }
        
        //JAVA16  @Override
        public int hashCode() {
            if (base == null) return 0;
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
    
    public static BigInteger bigint_add(BigInteger a, BigInteger b) {
        return a.add(b);
    }

    public static BigInteger bigint_sub(BigInteger a, BigInteger b) {
        return a.subtract(b);
    }

    public static BigInteger bigint_mul(BigInteger a, BigInteger b) {
        return a.multiply(b);
    }

    public static BigInteger bigint_div(BigInteger a, BigInteger b) {
        return a.divide(b);
    }

    public static BigInteger bigint_mod(BigInteger a, BigInteger b) {
        return a.mod(b);
    }

    public static BigInteger bigint_neg(BigInteger a) {
        return a.negate();
    }

    public static boolean bigint_lt(BigInteger a, BigInteger b) {
        return a.compareTo(b) < 0;
    }

    public static boolean bigint_le(BigInteger a, BigInteger b) {
        return a.compareTo(b) <= 0;
    }

    public static boolean bigint_gt(BigInteger a, BigInteger b) {
        return a.compareTo(b) > 0;
    }

    public static boolean bigint_ge(BigInteger a, BigInteger b) {
        return a.compareTo(b) >= 0;
    }

    public static boolean bigint_eq(BigInteger a, BigInteger b) {
        return a.compareTo(b) == 0;
    }

    public static boolean bigint_ne(BigInteger a, BigInteger b) {
        return a.compareTo(b) != 0;
    }

    public static boolean bigint_nonzero(BigInteger a) {
        return a.compareTo(BigInteger.ZERO) != 0;
    }

    public static float bigint_tofloat(BigInteger a) {
        return a.floatValue();
    }

    public static double bigint_todouble(BigInteger a) {
        return a.doubleValue();
    }

    public static long bigint_tolong(BigInteger a) {
        return a.longValue();
    }

    public static int bigint_toint(BigInteger a) {
        return a.intValue();
    }

    public static short bigint_toshort(BigInteger a) {
        return a.shortValue();
    }

    public static byte bigint_tobyte(BigInteger a) {
        return a.byteValue();
    }

    public static Real bigint_toreal(BigInteger a) {
        return new Real(a.doubleValue());
    }

    public static BigInteger bigint_valueOf(long i) {
        return new BigInteger(Long.toString(i));
    }

    public static Real real_add(Real a, Real b) {
        return a.add(b);
    }

    public static Real real_sub(Real a, Real b) {
        return a.subtract(b);
    }

    public static Real real_mul(Real a, Real b) {
        return a.multiply(b);
    }

    public static Real real_div(Real a, Real b) {
        return a.divide(b);
    }

    public static Real real_mod(Real a, Real b) {
        return a.mod(b);
    }

    public static Real real_neg(Real a) {
        return a.neg();
    }

    public static boolean real_lt(Real a, Real b) {
        return a.compareTo(b) < 0;
    }

    public static boolean real_le(Real a, Real b) {
        return a.compareTo(b) <= 0;
    }

    public static boolean real_gt(Real a, Real b) {
        return a.compareTo(b) > 0;
    }

    public static boolean real_ge(Real a, Real b) {
        return a.compareTo(b) >= 0;
    }

    public static boolean real_eq(Real a, Real b) {
        return a.compareTo(b) == 0;
    }

    public static boolean real_ne(Real a, Real b) {
        return a.compareTo(b) != 0;
    }

    public static boolean real_nonzero(Real a) {
        return a.compareTo(Real.ZERO) != 0;
    }

    public static Real real_valueOf(double i) {
        return Real.valueOf(i);
    }

    public static double real_todouble(Real a) {
        return a.doubleValue();
    }

    public static float real_tofloat(Real a) {
        return (float)a.doubleValue();
    }

    public static <T> T[] copyArray(T[] o) {
        T[] n = Arrays.copyOf(o,o.length);
        return n;
    }
    
    public static byte[] copyByteArray(byte[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    public static int[] copyIntArray(int[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    public static short[] copyShortArray(short[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    public static char[] copyCharArray(char[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    public static boolean[] copyBooleanArray(boolean[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    public static double[] copyDoubleArray(double[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    public static float[] copyFloatArray(float[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    public boolean print(String msg) {
        System.out.println(msg);
        return true;
    }
}
