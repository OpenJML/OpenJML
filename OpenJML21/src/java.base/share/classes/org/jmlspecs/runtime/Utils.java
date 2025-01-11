/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */

package org.jmlspecs.runtime;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.jmlspecs.lang.*;
import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.runtime.JmlAssertionError.Precondition;
import org.jmlspecs.lang.internal.TYPE;

/** 
 * This class contains utility methods used in internal translations for both
 * ESC and RAC.  In RAC, these functions are executed to provide the built-in
 * functionality; in ESC, the specifications written here are used to provide
 * background predicate logic for built-in functionality. 
 * @author David Cok
 */
public class Utils {
    public static int numVerificationErrors = 0;   

    public static final String RUNTIME = "org.jmlspecs.runtime";
    public static final String ASSERTION_FAILURE = "assertionFailureL"; // Must match the method name
    public static final String ASSERTION_FAILURE_EX = "assertionFailureE"; // Must match the method name
    public static final String REPORT_EXCEPTION = "reportException"; // must match method name
    public static final String racpropertyname = "org.jmlspecs.openjml.rac";
    public static final String racpropertyvalue = System.getProperty(racpropertyname);

    public Utils() {
        // TODO Auto-generated constructor stub
    }
    /** Determines whether to report assertion failures as exceptions (true)
     * or error messages (false).
     */
    public static boolean useExceptions = "exception".equals(racpropertyvalue);
    
    /** Determines whether to report assertion failures as AssertionError (true)
     * or error messages (false).
     */
    public static boolean useJavaException = "assertionerror".equals(racpropertyvalue);

    public static boolean useJavaAssert = "javaassert".equals(racpropertyvalue);

    /** If true, then error messages reporting assertion failures are 
     * accompanied with a stack trace to log.errorWriter.
     */
    public static boolean showStack = "showstack".equals(racpropertyvalue);
    
    public static boolean useStdout = racpropertyvalue == null || "stdout".equals(racpropertyvalue);
    static {
        if (!useStdout && !showStack && !useExceptions && !useJavaException && !useJavaAssert) {
            System.out.println("Invalid value for property " + racpropertyname + ": " + racpropertyvalue);
        }
    }
    /** If defined, gives the exit code to use if there are RAC errors */
    public static String racExitCodeString = "org.jmlspecs.openjml.racexitcode";
    
    // FIXME - what are these for - are they used?
    static final public String invariantMethodString = "_JML$$$checkInvariant";
    static final public String staticinvariantMethodString = "_JML$$$checkStaticInvariant";
    
    /** Reports a JML assertion without a specific label indicating the kind of assertion failure */
    public static void assertionFailure(String message) {
        assertionFailureL(message,null);
    }
    
    /** Reports a JML assertion failure with optional additional information
     * @param message the message to report
     * @param optMessage possibly null additional information
     */
    public static void assertionFailure2(String message, /*@ nullable*/ String optMessage) {
        if (optMessage != null) message = message + " (" + optMessage + ")";
        assertionFailure(message);
    }
    
    /** Reports a JML assertion (any JML precondition, postcondition, etc.)
     * failure with the given message.
     * @param message The message to report
     */
    // This one is declared first to minimize changes to its location 
    public static void assertionFailureL(String message, /*@ nullable */String label) {
        countVerificationErrors(); 
        if (Utils.useExceptions) {
            throw createException(message,label); // locB in RacBase
        } else if (Utils.showStack) { 
        	Error e = createException(message,label); // locC in RacBase
        	e.printStackTrace(System.out);
        } else if (Utils.useJavaException) {
            throw new java.lang.AssertionError(message);
        } else if (Utils.useJavaAssert) {
            assert false: message;
        } else {
    	   System.out.println(message); System.out.flush();
        }
    }
    
    /** This version of runtime assertion reporting reports only using exceptions */
    public static void assertionFailureE(String message, /*@ nullable */String label) {
        countVerificationErrors();
        throw createException(message,label);
    }
    
    /** Helper method to create the appropriate class of JmlAssertion */
    static private Error createException(String message, /*@ nullable */String label) {
        String exname = System.getProperty("org.openjml.exception."+label);
        if (exname == null) {
            exname = "org.jmlspecs.runtime.JmlAssertionError" + "$" + label;
        }
        Class<?> c;
        try { c = Class.forName(exname); } catch (ClassNotFoundException e) { c = null; }
        if (c != null) {
            try {
                @SuppressWarnings("unchecked")
                Constructor<? extends Error> cc = ((Class<? extends Error>)c).getConstructor(String.class,String.class);
                if (cc != null) {
                    Error e = cc.newInstance(message,label);
                    e.fillInStackTrace(); // locD in RacBase
                    return e;
                }
            } catch (ClassCastException e) {
                return new JmlAssertionError("User-defined JML assertion is not a subtype of java.lang.Error: " + exname
                        + System.getProperty("line.separator") + "    " + message, label);
            } catch (NoSuchMethodException e) {
                return new JmlAssertionError(message,label);
            } catch (InstantiationException e) {
                return new JmlAssertionError(message,label);
            } catch (InvocationTargetException e) {
                return new JmlAssertionError(message,label);
            } catch (IllegalAccessException e) {
                return new JmlAssertionError(message,label);
            }
        }
        return new JmlAssertionError(message,label); // locA in RacBase
    }
    
    static public void convertPrecondition(Precondition ex) {
        throw new Precondition(ex);
    }
    
    /** Used to create empty lists for RAC handling of loops */
    //@ public normal_behavior
    //@    ensures \result.size() == 0;
    static public /*@non_null pure */ <E> org.jmlspecs.lang.JMLList<E> defaultEmpty() {
        return null;
    }
    
    /** Returns true if the given class, found on the current classpath, if compiled with RAC */
    public static boolean isRACCompiled(Class<?> clazz) {
    	// The class named here must match that used in JmlCompiler.java 
        return null != clazz.getAnnotation(org.jmlspecs.annotation.RACCompiled.class);
    }

    /** Reports a JML assertion failure with the given message if the second argument is null
     * @param message the message to report if the second argument is null
     * @param v value to be tested 
     * @return the object which is the last argument
     */
    //@ ensures \result == v;
    @Nullable public static <T> T nonNullCheck(@Nullable String message, @Nullable T v) {
        if (v == null) assertionFailure(message);
        return v;
    }
    
    /** Reports a JML assertion failure with the given message if the second argument is false
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
    
    /** Reports a JML assertion with the given message if the given value is
     * not within the given range (inclusive), otherwise returns the last argument.
     */
    public static int intRangeCheck(String message, int low, int high, int v) {
        if (!(low <= v && v <= high)) assertionFailure(message);
        return v;
    }
    
    /** Reports a JML assertion with the given message if the given value is 0,
     * otherwise returns the value.
     */
    public static int zeroIntCheck(String message, int v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    /** Reports a JML assertion with the given message if the given value is 0,
     * otherwise returns the value.
     */
    public static long zeroLongCheck(String message, long v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    /** Reports a JML assertion with the given message if the given value is 0,
     * otherwise returns the value.
     */
    public static double zeroDoubleCheck(String message, double v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    /** Reports a JML assertion with the given message if the given value is 0,
     * otherwise returns the value.
     */
    public static float zeroFloatCheck(String message, float v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    /** Reports a JML assertion with the given message if the given value is 0,
     * otherwise returns the value.
     */
    public static short zeroShortCheck(String message, short v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    /** Reports a JML assertion with the given message if the given value is 0,
     * otherwise returns the value.
     */
    public static byte zeroByteCheck(String message, byte v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    /** Reports a JML assertion with the given message if the given value is 0,
     * otherwise returns the value.
     */
    public static char zeroCharCheck(String message, char v) {
        if (v == 0) assertionFailure(message);
        return v;
    }
    
    /** Returns the name of the class of the argument */
    public static String typeName(Throwable t) {
        return t.getClass().toString();
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
    
    // The report... methods provide a mechanism for reporting
    // values encountered during execution.
    
    /** Just prints out a message */
    public static void report(String str) {
        System.out.println(str);
    }
    
    public static void reportNoSuchField(NoSuchFieldError t, @Nullable String location) {
    	t.printStackTrace();
        String msg = t.getMessage();
        int k = msg.indexOf('(');
        if (k >= 0) msg = msg.substring(0,k);
        msg = "Skipping a specification clause because it contains an uncompiled ghost or model field: " + msg;
        if (location != null) msg = msg + " (" + location + ")";
        report(msg);
    }
    
    public static void reportNoSuchMethod(NoSuchMethodError t, @Nullable String location) {
        String msg = t.getMessage();
        int k = msg.indexOf('(');
        if (k >= 0) msg = msg.substring(0,k);
        msg = "Skipping a specification clause because it contains an uncompiled model method: " + msg;
        if (location != null) msg = msg + " (" + location + ")";
        t.printStackTrace(System.out);
        report(msg);
    }
    
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
        report("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a short value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static short reportShort(String key, short v) {
        report("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a char value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static char reportChar(String key, char v) {
        report("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a long value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static long reportLong(String key, long v) {
        report("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a float value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static float reportFloat(String key, float v) {
        report("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a double value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static double reportDouble(String key, double v) {
        report("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a boolean value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static boolean reportBoolean(String key, boolean v) {
        report("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a int value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static int reportInt(String key, int v) {
        report("LABEL " + key + " = " + v);
        return v;
    }

    /** Reports a Object value under the given key
     * @param key the identifier for the value
     * @param v the value to report
     * @return the value of v
     */
    public static Object reportObject(String key, Object v) {
        report("LABEL " + key + " = " + v);
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
    
//    public static boolean equalTYPE(IJMLTYPE t1, IJMLTYPE t2) {
//        if (t1 == t2) return true;
//        if (t1 == null || t2 == null) return false;
//        return t1.equals(t2);
//    }
//    
//
//    // TODO - document - this and following
//    public static @NonNull IJMLTYPE makeTYPE(@NonNull Class<?> base, @NonNull IJMLTYPE... args) {
//        return JmlTypeRac.make(base,args);
//    }
//    
//    public static  IJMLTYPE makeTYPEN(Class<?> base) {
//        return JmlTypeRac.make(base,null);
//    }
//    
//    public static  IJMLTYPE makeTYPEQ() {
//        return JmlTypeRac.make(null,null);
//    }
//    
//    public static final IJMLTYPE[] emptyArgs = {};
//    
//    public static @NonNull IJMLTYPE makeTYPE0(@NonNull Class<?> base) {
//        if (base == null) return null;
//        return JmlTypeRac.make(base,emptyArgs);
//    }
//    
//    public static @NonNull IJMLTYPE makeTYPE1(@NonNull Class<?> base, @NonNull IJMLTYPE a0) {
//        if (base == null) return null;
//        return JmlTypeRac.make(base,new IJMLTYPE[]{a0});
//    }
//    
//    public static @NonNull IJMLTYPE makeTYPE2(@NonNull Class<?> base, @NonNull IJMLTYPE a0, @NonNull IJMLTYPE a1) {
//        if (base == null) return null;
//        return JmlTypeRac.make(base,new IJMLTYPE[]{a0,a1});
//    }
//    
//    public static  Class<?> erasure(IJMLTYPE t) {
//        return t.erasure();
//    }
//    
//    public static IJMLTYPE[] typeargs(IJMLTYPE t) {
//        return t.typeargs();
//    }
//    
//    public static boolean isArray(IJMLTYPE t) {
//        return t.erasure().isArray();
//    }
//    
//    public static Class<?> getJavaComponentType(Class<?> t) {
//        return (t.getComponentType());
//    }
//    
//    public static IJMLTYPE getJMLComponentType(IJMLTYPE t) {
//        return makeTYPE0(t.erasure().getComponentType());
//    }
//    
//    
    public static String getClassName(Object o) {
        return o.getClass().getName();
    }
    
    public static String concat(String s1, String s2) {
        return s1 + s2;
    }
//    
//    public static boolean isSubTypeOf(IJMLTYPE t, IJMLTYPE tt) {
//        try {
//            return tt.erasure().isAssignableFrom(t.erasure());
//        } catch (java.lang.IncompatibleClassChangeError e) {
//            System.err.println("ISTO: " + t.erasure() + " " + tt.erasure());
//            return false;
//        }
//    }
//    
//    public static boolean isEqualTo(IJMLTYPE t, IJMLTYPE tt) {
//        if (t == tt) return true;
//        if (t == null || tt == null) return false;
//        return tt.erasure() == t.erasure();
//    }
    
    public static <T> Iterator<T> iterator(Iterable<T> iterable) {
        return iterable.iterator();
    }
    
    public static <T> T next(Iterator<T> iterable) {
        return iterable.next();
    }
    
    public static boolean hasNext(Iterator<?> iterable) {
        return iterable.hasNext();
    }
    
//    // TODO - document this and following
//    private static class JmlTypeRac implements IJMLTYPE {
//
//        final private Class<?> base;
//        final private IJMLTYPE[] args;
//        final private static Map<IJMLTYPE,IJMLTYPE> internSet = new HashMap<IJMLTYPE,IJMLTYPE>();
//        
//        public static IJMLTYPE make(Class<?> base, IJMLTYPE[] args) {
//            JmlTypeRac t = new JmlTypeRac(base,args);
//            return t.intern();
//        }
//        
//        public String toString() {
//            if (base == null) return "?"; // FIXME - really this is just unknown, not a wildcard
//            String s = base.toString();
//            if (args != null && args.length > 0) {
//                s = s + "<";
//                boolean first = true;
//                for (IJMLTYPE t: args) {
//                    if (first) first = false; else s = s + ",";
//                    s = s + t.toString();
//                }
//                s = s + ">";
//            }
//            return s;
//        }
//        
//        private IJMLTYPE intern() {
//            IJMLTYPE tt = internSet.get(this);
//            if (tt == null) {
//                tt = this;
//                internSet.put(this,this);
//            }
//            return tt;
//        }
//        
//        private JmlTypeRac(Class<?> base, IJMLTYPE... args) {
//            this.base = base;
//            this.args = args;
//        }
//
//        @Override
//        public IJMLTYPE[] typeargs() {
//            return args;
//        }
//
//        @Override
//        public boolean equals(IJMLTYPE t) {
//            return isEqualTo(this,t);
//        }
//        
//        //JAVA16  @Override
//        public int hashCode() {
//            if (base == null) return 0;
//            int i = base.hashCode();
//            int k = 0;
//            for (IJMLTYPE t: args) i = i + (t.hashCode()<< (++k));
//            return i;
//        }
//
//        @Override
//        public Class<?> erasure() {
//            return base;
//        }
//
//        @Override
//        public boolean isArray() {
//            return base.isArray();
//        }
//
//        @Override
//        public boolean isSubtypeOf(IJMLTYPE t) {
//            return t.erasure().isAssignableFrom(this.base);
//        }
//        
//        @Override  // FIXME - does not work for arrays of JML types with type arguments.
//        public IJMLTYPE getComponentType() {
//            if (!base.isArray()) return null;
//            return Utils.getJMLComponentType(this);
//        }
//
//    }
    
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
    

    /** Makes a new copy of the argument */
    public static <T> T[] copyArray(T[] o) {
        T[] n = Arrays.copyOf(o,o.length);
        return n;
    }
    
    /** Makes a new copy of the argument */
    public static byte[] copyByteArray(byte[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    /** Makes a new copy of the argument */
    public static int[] copyIntArray(int[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    /** Makes a new copy of the argument */
    public static short[] copyShortArray(short[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    /** Makes a new copy of the argument */
    public static char[] copyCharArray(char[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    /** Makes a new copy of the argument */
    public static boolean[] copyBooleanArray(boolean[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    /** Makes a new copy of the argument */
    public static double[] copyDoubleArray(double[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    /** Makes a new copy of the argument */
    public static float[] copyFloatArray(float[] o) {
        return Arrays.copyOf(o,o.length);
    }
    
    public static String toStringObject(Object o) {
        return o == null ? "null" : o.toString();
    }
    
    public static String toStringBoolean(boolean b) {
        return Boolean.toString(b);
    }
    
    public static String toStringInt(int b) {
        return Integer.toString(b);
    }
    
    public static String toStringLong(long b) {
        return Long.toString(b);
    }
    
    public static String toStringShort(short b) {
        return Short.toString(b);
    }
    
    public static String toStringByte(byte b) {
        return Byte.toString(b);
    }
    
    public static String toStringFloat(float b) {
        return Float.toString(b);
    }
    
    public static String toStringDouble(double b) {
        return Double.toString(b);
    }
    
    public static String toStringChar(char b) {
        return Character.toString(b);
    }
    
    static public class NoModelMethodImplementationException extends RuntimeException {
        private static final long serialVersionUID = 1L;
        public NoModelMethodImplementationException(String name) {
            super("No model method implementation found for " + name);
        }
    }
    
    public static void noModelMethodImplementation(String name) {
        throw new NoModelMethodImplementationException(name);
    }
    
    /** Used just for debugging - a breakpoint is kept set within the method */
    public boolean print(String msg) {
        System.out.println(msg);
        return true;
    }
    
    public static void countVerificationErrors() {
        final String racExitCode = System.getProperty(racExitCodeString);
        if (numVerificationErrors == 0 && racExitCode != null) {
            Thread t = new Thread() {
                @Override
                public void run() {
                    int exitcode = 1;
                    try {
                        exitcode = Integer.parseInt(racExitCode);
                    } catch (Exception e) {
                        // just continue
                    }
                    System.out.println(numVerificationErrors + " verification error" +
                            (numVerificationErrors>1?"s":""));
                    java.lang.Runtime.getRuntime().halt(exitcode);
                }
            };
            java.lang.Runtime.getRuntime().addShutdownHook(t);
        }
        numVerificationErrors++;
    }
    
    // FIXME - get rid of this and use TYPE.of in JmlTreeUtils
    public TYPE makeTYPE0(Class<?> clazz) {
        return TYPE.of(clazz, TYPE.noargs);
    }
}
