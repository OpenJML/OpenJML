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
    
    abstract public real add(real r);
    abstract public real subtract(real r);
    abstract public real multiply(real r);
    abstract public real divide(real r);
    abstract public real mod(real r);
    abstract public real negate();
    abstract public int compareTo(real r);
    
    public static real of(double v) { return proto.from(v); }
    public static real of(long v) { return proto.from(v); }
    public static real of(int v) { return proto.from(v); } // FIXME - have matching problems if this method is not present (cf. racfiles.racreal)
    public static real of(bigint v) { return proto.from(v); }
    public static real of(java.math.BigInteger v) { return proto.from(v); }
    
    abstract protected real from(double v);
    abstract protected real from(long v);
             protected real from(int v) { return from((long)v); }
    abstract protected real from(bigint v);
    abstract protected real from(java.math.BigInteger v);
    
    abstract public int intValue();
    abstract public long longValue();
    abstract public float floatValue();
    abstract public double doubleValue();
    abstract public bigint bigintValue();
    
    public boolean eq(real r) { return compareTo(r) == 0; }
    public boolean ne(real r) { return compareTo(r) != 0; }
    public boolean gt(real r) { return compareTo(r) > 0; }
    public boolean lt(real r) { return compareTo(r) < 0; }
    public boolean ge(real r) { return compareTo(r) >= 0; }
    public boolean le(real r) { return compareTo(r) <= 0; }
    
    abstract public String toString();
    
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
            return Double.valueOf(value).compareTo(Double.valueOf(((RealUsingDouble)o).value));
        }
        
        public RealUsingDouble from(double d) {
            return new RealUsingDouble(d);
        }

        public RealUsingDouble from(long d) {
            return new RealUsingDouble((double)d);
        }

        public RealUsingDouble from(int d) {
            return new RealUsingDouble((double)d);
        }

        public RealUsingDouble from(bigint d) {
            return from(d.bigValue());
        }

        public RealUsingDouble from(java.math.BigInteger d) {
            return from((double)(d.longValue())); // FIXME - could do better?
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
            return bigint.of((long)value); // FIXME - need to do better
        }
        
        @Override
        public String toString() {
            return Double.toString(value);
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
        public int compareTo(real r) {
            return value.compareTo(((RealUsingBigDecimal)r).value);
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
        public RealUsingBigDecimal from(int v) {
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
        public int intValue() {
            return value.intValue();
        }

        @Override
        public long longValue() {
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
    }
    
//    private static final long serialVersionUID = 1L;
//
//    protected double _double;
//    
//    private real(double d) { _double = d; }
//    
//    public real add(real r) {
//        return new real(_double + r._double);
//    }
//
//    public real subtract(real r) {
//        return new real(_double + r._double);
//    }
//
//    public real multiply(real r) {
//        return new real(_double * r._double);
//    }
//
//    public real divide(real r) {
//        return new real(_double / r._double);
//    }
//
//    public real mod(real r) {
//        return new real(_double % r._double);
//    }
//
//    public boolean eq(real r) {
//        return (_double == r._double);
//    }
//
//    public boolean ne(real r) {
//        return (_double != r._double);
//    }
//
//    public boolean gt(real r) {
//        return (_double > r._double);
//    }
//
//    public boolean ge(real r) {
//        return (_double >= r._double);
//    }
//
//    public boolean lt(real r) {
//        return (_double < r._double);
//    }
//
//    public boolean le(real r) {
//        return (_double <= r._double);
//    }
//
//    public real negate() {
//        return new real(-_double);
//    }
//
//    static public real of(double d) {
//        return new real(d);
//    }
//
//    static public real of(long d) {
//        return new real(d);
//    }
//
//    static public real of(int d) {
//        return new real(d);
//    }
//
//    static public real valueOf(long d) {
//        return new real(d);
//    }
//
//    static public real of(java.math.BigInteger d) {
//        return real.of(d.doubleValue());
//    }
//
//    static public real of(org.jmlspecs.lang.internal.bigint d) {
//        return real.of(d.bigValue().doubleValue());
//    }
//
//    public double doubleValue() {
//        return _double;
//    }
//
//    public float floatValue() {
//        return (float)_double;
//    }
//
//    public long longValue() {
//        return (long)_double;
//    }
//
//    public int intValue() {
//        return (int)_double;
//    }
//
//    public int compareTo(real r) {
//        return (_double == r._double) ? 0 : (_double < r._double) ? -1 : 1;
//    }
//    
//    static public real ZERO = real.of(0.0);
//    
//    public String toString() {
//        return Double.toString(_double);
//    }

}
