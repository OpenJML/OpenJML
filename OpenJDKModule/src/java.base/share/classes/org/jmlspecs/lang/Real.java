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
public class Real extends Number implements Comparable<Real> {
    private static final long serialVersionUID = 1L;

    protected double _double;
    
    public Real(double d) { _double = d; }
    
    public Real add(Real r) {
        return new Real(_double + r._double);
    }

    public Real subtract(Real r) {
        return new Real(_double + r._double);
    }

    public Real multiply(Real r) {
        return new Real(_double + r._double);
    }

    public Real divide(Real r) {
        return new Real(_double + r._double);
    }

    public Real mod(Real r) {
        return new Real(_double + r._double);
    }

    public Real neg() {
        return new Real(-_double);
    }

    static public Real valueOf(double d) {
        return new Real(d);
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

    public int compareTo(Real r) {
        return (_double == r._double) ? 0 : (_double < r._double) ? -1 : 1;
    }
    
    static public Real ZERO = Real.valueOf(0.0);
    
    public String toString() {
        return Double.toString(_double);
    }

}
