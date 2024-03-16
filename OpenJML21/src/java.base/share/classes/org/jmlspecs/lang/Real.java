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
public class real extends Number implements Comparable<real> {
    private static final long serialVersionUID = 1L;

    protected double _double;
    
    public real(double d) { _double = d; }
    
    public real add(real r) {
        return new real(_double + r._double);
    }

    public real subtract(real r) {
        return new real(_double + r._double);
    }

    public real multiply(real r) {
        return new real(_double + r._double);
    }

    public real divide(real r) {
        return new real(_double + r._double);
    }

    public real mod(real r) {
        return new real(_double + r._double);
    }

    public real neg() {
        return new real(-_double);
    }

    static public real valueOf(double d) {
        return new real(d);
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
    
    static public real ZERO = real.valueOf(0.0);
    
    public String toString() {
        return Double.toString(_double);
    }

}
