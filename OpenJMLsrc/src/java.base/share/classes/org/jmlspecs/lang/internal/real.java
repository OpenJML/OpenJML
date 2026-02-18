/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.lang.internal;

import java.math.BigDecimal;

/** This class is what \real is mapped to for RAC execution. The translation is built-in to JmlAssertionAdder
 * to translate any uses of \real to Java executable code. The name and package of this class are hard-wired,
 * as are the names of the methods. For eaxample r1 + r2 for two \real values is mapped to the 'add' method.
 * 
 * However, real is an abstract class and can be implemented in a variety of ways, each giving a different approximation
 * to the behavior of mathematical reals. The choice of the concrete implementation is set by the value with which 
 * 'proto' is initialized. Any such implementation class must derive from 'real', implementing its non-static methods 
 * however is appropriate. These implementations are ***not*** implemented to tolerate mixed versions of real; that is,
 * in a given executable, all compilation units must use the same concrete implementation of 'real'.
 */
public abstract class real extends Number implements org.jmlspecs.lang.IJmlPrimitiveType, Comparable<real> {

    private real() {}
    private static final long serialVersionUID = 1L;

    private static real proto = new RealUsingDouble();
    
    public static real empty() { return proto.from(0); }
    
    // FIXME - should these be protected
    abstract public real add(real r);
    abstract public real subtract(real r);
    abstract public real multiply(real r);
    abstract public real divide(real r);
    abstract public real mod(real r);
    abstract public real negate();
    abstract public int compareTo(real r);
    
    public static real of(double v) {
        if (!Double.isFinite(v)) org.jmlspecs.runtime.Utils.assertionFailure("JML double value cast to real is not finite");
        return proto.from(v);
    }
    public static real of(float v) {
        if (!Float.isFinite(v)) org.jmlspecs.runtime.Utils.assertionFailure("JML float value cast to real is not finite");
        return proto.from(v);
    }
    public static real of(long v) { return proto.from(v); }
    public static real of(int v) { return proto.from(v); } // FIXME - have matching problems if this method is not present (cf. racfiles.racreal)
    public static real of(char v) { return proto.from(v); } // FIXME - have matching problems if this method is not present (cf. racfiles.racreal)
    public static real of(short v) { return proto.from(v); } // FIXME - have matching problems if this method is not present (cf. racfiles.racreal)
    public static real of(byte v) { return proto.from(v); } // FIXME - have matching problems if this method is not present (cf. racfiles.racreal)
    public static real of(bigint v) { return proto.from(v); }
    public static real of(java.math.BigInteger v) { return proto.from(v); }
    public static real of(java.math.BigDecimal v) { return proto.from(v); }
    
    abstract protected real from(double v);
    abstract protected real from(long v);
             protected real from(int v) { return from((long)v); }
    abstract protected real from(bigint v);
    abstract protected real from(java.math.BigInteger v);
    abstract protected real from(java.math.BigDecimal v);
    
    @Override
             public byte byteValue() {
                return (byte)intValue();
            }
    @Override
             public short shortValue() { 
                return (short)intValue();
             }
    
             public char charValue() {
                     return (char)intValue();
             }
    @Override
    abstract public int intValue();
    @Override
    abstract public long longValue();
    @Override
    abstract public float floatValue();
    @Override
    abstract public double doubleValue();
    abstract public bigint bigintValue();
    
    public boolean eq(real r) { return compareTo(r) == 0; }
    public boolean ne(real r) { return compareTo(r) != 0; }
    public boolean gt(real r) { return compareTo(r) > 0; }
    public boolean lt(real r) { return compareTo(r) < 0; }
    public boolean ge(real r) { return compareTo(r) >= 0; }
    public boolean le(real r) { return compareTo(r) <= 0; }
    
    @Override
    abstract public String toString();
    @Override
    abstract public int hashCode();
    
    public boolean equals(real r) { return eq(r); }
    
    @Override
    public boolean equals(/*@ nullable */Object o) { return o instanceof real r && eq(r); }
    
    public static class RealUsingDouble extends real {
        public static final long serialVersionUID = 1L;

        final private double value;
        
        private RealUsingDouble() {
            value = 0;
        }
        private RealUsingDouble(double r) {
            value = r;
        }
        
        @Override
        public real add(real r) {
            return new RealUsingDouble(value + ((RealUsingDouble)r).value);
        }

        @Override
        public real subtract(real r) {
            return new RealUsingDouble(value - ((RealUsingDouble)r).value);
        }

        @Override
        public real multiply(real r) {
            return new RealUsingDouble(value * ((RealUsingDouble)r).value);
        }

        @Override
        public real divide(real r) {
            return new RealUsingDouble(value / ((RealUsingDouble)r).value);
        }

        @Override
        public real mod(real r) {
            return new RealUsingDouble(value % ((RealUsingDouble)r).value);
        }

        public real negate() {
            return new RealUsingDouble(-value);
        }
        
        @Override
        public int compareTo(real o) {
            if (o == null) throw new NullPointerException("\\real.compareTo(null)");
            if (o instanceof RealUsingDouble r) return ((Double)value).compareTo(r.value);
            throw new IllegalArgumentException("\\real.compareTo called with a value that is not a RealUsingDouble");
        }
        
        public RealUsingDouble from(double d) { // FIXME - check for NaN and infinity?
            return new RealUsingDouble(d);
        }

        public RealUsingDouble from(long d) {
            return new RealUsingDouble((double)d);
        }

        public RealUsingDouble from(bigint d) {
            return from(d.bigValue());
        }

        public RealUsingDouble from(java.math.BigInteger d) {
            return from(d.doubleValue());
        }

        public RealUsingDouble from(java.math.BigDecimal d) {
            return from(d.doubleValue());
        }

        @Override
        public int intValue() {
            return (int)value;
        }

        @Override
        public long longValue() {
            return (long)value;
        }

        @Override
        public float floatValue() {
            return (float)value;
        }

        @Override
        public double doubleValue() {
            return value;
        }
        
        @Override
        public bigint bigintValue() {
            return bigint.of(java.math.BigDecimal.valueOf(value).toBigInteger());
        }
        
        @Override
        public String toString() {
            return Double.toString(value);
        }
        
        @Override
        public int hashCode() {
            return ((Double)value).hashCode();
        }
    }
    
    public static class RealUsingBigDecimal extends real {
        public static final long serialVersionUID = 1L;

        final private java.math.BigDecimal value;
        
        private RealUsingBigDecimal() {
            value = BigDecimal.ZERO;
        }
        
        private RealUsingBigDecimal(java.math.BigDecimal r) {
            value = r;
        }
        
        @Override
        public real add(real r) {
            return new RealUsingBigDecimal(value.add(((RealUsingBigDecimal)r).value));
        }

        @Override
        public real subtract(real r) {
            return new RealUsingBigDecimal(value.subtract(((RealUsingBigDecimal)r).value));
        }

        @Override
        public real multiply(real r) {
            return new RealUsingBigDecimal(value.multiply(((RealUsingBigDecimal)r).value));
        }

        @Override
        public real divide(real r) {
            return new RealUsingBigDecimal(value.divide(((RealUsingBigDecimal)r).value));
        }

        @Override
        public real mod(real r) {
            BigDecimal rv = ((RealUsingBigDecimal)r).value;
            java.math.BigDecimal v = value.subtract(value.divideToIntegralValue(rv).multiply(rv));
            return new RealUsingBigDecimal(v);
        }

        @Override
        public real negate() {
            return new RealUsingBigDecimal(value.negate());
        }

        @Override
        public int compareTo(real o) {
            if (o == null) throw new NullPointerException("\\real.compareTo(null)");
            if (o instanceof RealUsingBigDecimal r) return value.compareTo(r.value);
            throw new IllegalArgumentException("\\real.compareTo called with a value that is not a RealUsingBigDecimal");
        }
        
        @Override
        public RealUsingBigDecimal from(double v) {
            return new RealUsingBigDecimal(new BigDecimal(v));
        }

        @Override
        public RealUsingBigDecimal from(long v) {
            return new RealUsingBigDecimal(new BigDecimal(v));
        }

        @Override
        public RealUsingBigDecimal from(bigint v) {
            return new RealUsingBigDecimal(new BigDecimal(v.bigValue()));
       }

        @Override
        public RealUsingBigDecimal from(java.math.BigInteger v) {
            return new RealUsingBigDecimal(new BigDecimal(v));
       }

        @Override
        public RealUsingBigDecimal from(java.math.BigDecimal v) {
            return new RealUsingBigDecimal(v);
       }

        @Override
        public byte byteValue() {
            if (of(Byte.MIN_VALUE).gt(this) || of(Byte.MAX_VALUE).lt(this)) org.jmlspecs.runtime.Utils.assertionFailure("JML argument to numeric cast is out of range of the target type: " + this + " to byte");
            return (byte)value.intValue();
        }

        @Override
        public char charValue() {
            if (of(Character.MIN_VALUE).gt(this) || of(Character.MAX_VALUE).lt(this)) org.jmlspecs.runtime.Utils.assertionFailure("JML argument to numeric cast is out of range of the target type: " + this + " to char");
            return (char)value.intValue();
        }

        @Override
        public short shortValue() {
            if (of(Short.MIN_VALUE).gt(this) || of(Short.MAX_VALUE).lt(this)) org.jmlspecs.runtime.Utils.assertionFailure("JML argument to numeric cast is out of range of the target type: " + this + " to short");
            return (short)value.intValue();
        }

        @Override
        public int intValue() {
            if (of(Integer.MIN_VALUE).gt(this) || of(Integer.MAX_VALUE).lt(this)) org.jmlspecs.runtime.Utils.assertionFailure("JML argument to numeric cast is out of range of the target type: " + this + " to int");
            return value.intValue();
        }

        @Override
        public long longValue() {
            if (of(Long.MIN_VALUE).gt(this) || of(Long.MAX_VALUE).lt(this)) org.jmlspecs.runtime.Utils.assertionFailure("JML argument to numeric cast is out of range of the target type: " + this + " to long");
            return value.longValue();
        }

        @Override
        public float floatValue() {
            return value.floatValue();
        }

        @Override
        public double doubleValue() {
            return value.doubleValue();
        }

        @Override
        public bigint bigintValue() {
            return bigint.of(value.toBigInteger());
        }
        
        @Override
        public String toString() {
            return value.toString();
        }
        
        @Override
        public int hashCode() {
            return value.hashCode();
        }
    }

}
