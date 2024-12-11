/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.lang;

/** This is an implementation of 'real Reals', intended to be the RAC implementation
 * of \real and the boxed version of \real. It is currently implemented as a 
 * double, but that could be improved to big rationals or big decimals. We need
 * a class different from Double, both because we want to improve on the double
 * implementation and because Double can't unbox to both double and \real.
 */
public class real implements IJmlPrimitiveType {
    
    public static class Real extends Number implements Comparable<Real> {
        public static final long serialVersionUID = 1L;

        final private double value;
        
        private Real(double r) {
            value = r;
        }
        
        public Real add(Real r) {
            return new Real(value + r.value);
        }

        public Real subtract(Real r) {
            return new Real(value - r.value);
        }

        public Real multiply(Real r) {
            return new Real(value * r.value);
        }

        public Real divide(Real r) {
            return new Real(value / r.value);
        }

        public Real mod(Real r) {
            return new Real(value % r.value);
        }

        public Real neg() {
            return new Real(-value);
        }
        
        @Override
        public int compareTo(Real o) {
            return Double.valueOf(value).compareTo(Double.valueOf(o.value));
        }
        
        public static Real of(double d) {
            return new Real(d);
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
        
    }
//    public static class Real extends Number implements Comparable<Real> {
//        public static final long serialVersionUID = 1L;
//
//        final private java.math.BigDecimal value;
//        
//        private Real(java.math.BigDecimal r) {
//            value = r;
//        }
//        
//        public Real add(Real r) {
//            return new Real(value.add(r.value));
//        }
//
//        public Real subtract(Real r) {
//            return new Real(value.subtract(r.value));
//        }
//
//        public Real multiply(Real r) {
//            return new Real(value.multiply(r.value));
//        }
//
//        public Real divide(Real r) {
//            return new Real(value.divide(r.value));
//        }
//
//        public Real mod(Real r) {
//            java.math.BigDecimal v = value.subtract(value.divideToIntegralValue(r.value).multiply(r.value));
//            return new Real(v);
//        }
//
//        public Real neg() {
//            return new Real(value.negate());
//        }
//        @Override
//        public int compareTo(Real o) {
//            // TODO Auto-generated method stub
//            return 0;
//        }
//        
//        @Override
//        public static Real of(double d) {
//            
//        }
//
//        @Override
//        public int intValue() {
//            // TODO Auto-generated method stub
//            return 0;
//        }
//
//        @Override
//        public long longValue() {
//            // TODO Auto-generated method stub
//            return 0;
//        }
//
//        @Override
//        public float floatValue() {
//            // TODO Auto-generated method stub
//            return 0;
//        }
//
//        @Override
//        public double doubleValue() {
//            // TODO Auto-generated method stub
//            return 0;
//        }
//        
//    }
    
    private static final long serialVersionUID = 1L;

    protected double _double;
    
    private real(double d) { _double = d; }
    
    public real add(real r) {
        return new real(_double + r._double);
    }

    public real subtract(real r) {
        return new real(_double + r._double);
    }

    public real multiply(real r) {
        return new real(_double * r._double);
    }

    public real divide(real r) {
        return new real(_double / r._double);
    }

    public real mod(real r) {
        return new real(_double % r._double);
    }

    public boolean eq(real r) {
        return (_double == r._double);
    }

    public boolean ne(real r) {
        return (_double != r._double);
    }

    public boolean gt(real r) {
        return (_double > r._double);
    }

    public boolean ge(real r) {
        return (_double >= r._double);
    }

    public boolean lt(real r) {
        return (_double < r._double);
    }

    public boolean le(real r) {
        return (_double <= r._double);
    }

    public real negate() {
        return new real(-_double);
    }

    static public real of(double d) {
        return new real(d);
    }

    static public real of(long d) {
        return new real(d);
    }

    static public real of(int d) {
        return new real(d);
    }

    static public real valueOf(long d) {
        return new real(d);
    }

    static public real of(java.math.BigInteger d) {
        return real.of(d.doubleValue());
    }

    static public real of(org.jmlspecs.lang.internal.bigint d) {
        return real.of(d.bigValue().doubleValue());
    }

    public double doubleValue() {
        return _double;
    }

    public float floatValue() {
        return (float)_double;
    }

    public long longValue() {
        return (long)_double;
    }

    public int intValue() {
        return (int)_double;
    }

    public int compareTo(real r) {
        return (_double == r._double) ? 0 : (_double < r._double) ? -1 : 1;
    }
    
    static public real ZERO = real.of(0.0);
    
    public String toString() {
        return Double.toString(_double);
    }

}
