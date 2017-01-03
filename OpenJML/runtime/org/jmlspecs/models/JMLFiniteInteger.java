// @(#)$Id: JMLFiniteInteger.java,v 1.22 2007/02/08 14:05:50 leavens Exp $

// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.


package org.jmlspecs.models;

import java.math.BigInteger;

/** Arbitrary precision integers with a finite value.
 *
 * @version $Revision: 1.22 $
 * @author Gary T. Leavens
 * @see java.math.BigInteger
 */
//-@ immutable
public /*@ pure @*/ class JMLFiniteInteger extends JMLInfiniteIntegerClass {

    protected final /*@ non_null */ BigInteger val;
    //@                   in sign, finite_value, is_infinite;

    //@ protected represents finite_value <- val;
    //@ protected represents sign <- val.signum();
    //@ protected represents is_infinite <- false;

    //@ public invariant !is_infinite;

    /** The number zero (0).
     */
    public static final JMLFiniteInteger ZERO
        = new JMLFiniteInteger();

    /** The number one (1).
     */
    public static final JMLFiniteInteger ONE
        = new JMLFiniteInteger(BigInteger.ONE);

    /** Initialize this finite integer to zero (0).
     */
    /*@ public normal_behavior
      @    assignable nonnegative, sign, is_infinite, finite_value;
      @    ensures !is_infinite;
      @    ensures finite_value.equals(BigInteger.ZERO);
	also private normal_behavior
	   modifies val;
      @*/
    public JMLFiniteInteger() { val = BigInteger.ZERO; }

    /** Initialize this finite integer from the given BigInteger.
     */
    /*@ public behavior
      @    assignable nonnegative, sign, is_infinite, finite_value;
      @    ensures !is_infinite && finite_value.equals(n);
      @    signals_only IllegalArgumentException;
      @    signals (IllegalArgumentException) n == null;
      @*/
    public JMLFiniteInteger(/*@ non_null @*/ BigInteger n)
        throws IllegalArgumentException
    {
        if (n != null) {
            val = n;
        } else {
            throw new IllegalArgumentException();
        }
    }

    /** Initialize this finite integer from the given long.
     */
    public JMLFiniteInteger(long n) { val = BigInteger.valueOf(n); }

    /** Return the sign of this integer.
     */
    public int signum() { return val.signum(); }

    /** Return true.
     */
    public boolean isFinite() { return true; }

    /** Return the value of this integer.
     */
    public BigInteger finiteValue() { return val; }

    /** Compare this to the given integer, returning a comparison code.
     */
    public int compareTo(JMLInfiniteInteger n) {
        //@ assume n != null;
        if (n instanceof JMLFiniteInteger) {
            return val.compareTo(((JMLFiniteInteger)n).val);
        } else {
            return -1 * n.signum();
        }
    }

    /** Compare this to o, returning a comparison code.
     *  @param o the object this is compared to.
     *  @exception ClassCastException when o is not
     *             a JMLInfiniteInteger or a BigInteger.
     */
    public int compareTo(/*@ non_null @*/ Object o) 
            throws NullPointerException, ClassCastException
    {
        if (o == null) {
            throw new NullPointerException();
        } else if (o instanceof BigInteger) {
            return val.compareTo((BigInteger)o);
        } else if (o instanceof JMLFiniteInteger) {
            return val.compareTo(((JMLFiniteInteger)o).val);
        } else if (o instanceof JMLPositiveInfinity) {
            return -1;
        } else if (o instanceof JMLNegativeInfinity) {
            return +1;
        } else {
            throw new ClassCastException();
        }
    }

    /** Return a hash code for this object.
     */
    public int hashCode() { return val.hashCode(); }

    /** Return the negation of this integer.
     */
    public JMLInfiniteInteger negate() {
        BigInteger n = val.negate();
        //@ assume n != null;
        return new JMLFiniteInteger(n);
    }

    /** Return the sum of this integer and the argument.
     */
    public JMLInfiniteInteger add(JMLInfiniteInteger n) {
        //@ assume n != null;
        if (n instanceof JMLFiniteInteger) {
            BigInteger s = val.add(((JMLFiniteInteger)n).val);
            //@ assume s != null;
            return new JMLFiniteInteger(s);
        } else {
            return n;
        }
    }

    /** Return the difference between this integer and the argument.
     */
    public JMLInfiniteInteger subtract(JMLInfiniteInteger n) {
        //@ assume n != null;
        if (n instanceof JMLFiniteInteger) {
            BigInteger s = val.subtract(((JMLFiniteInteger)n).val);
            //@ assume s != null;
            return new JMLFiniteInteger(s);
        } else {
            return n.negate();
        }
    }

    /** Return the product of this integer and the argument.
     */
    public JMLInfiniteInteger multiply(JMLInfiniteInteger n) {
        //@ assume n != null;
        if (n instanceof JMLFiniteInteger) {
            BigInteger s = val.multiply(((JMLFiniteInteger)n).val);
            //@ assume s != null;
            return new JMLFiniteInteger(s);
        } else if (val.equals(BigInteger.ZERO)) {
            return ZERO; //FIXME - ZERO * infinity ????
        } else if (val.signum() == +1) {
            return n;
        } else {
            JMLInfiniteInteger ret = n.negate();
            //@ assume ret != null;
            return ret;
        }
    }

    /** Return the quotient of this integer divided by the argument.
     */
    public JMLInfiniteInteger divide(JMLInfiniteInteger n) {
        //@ assume n != null;
        if (n instanceof JMLFiniteInteger) {
            BigInteger s = val.divide(((JMLFiniteInteger)n).val);
            //@ assume s != null;
            return new JMLFiniteInteger(s);
        } else {
            return ZERO;
        }
    }

    /** Return the remainder of this integer divided by the argument.
     */
    public JMLInfiniteInteger remainder(JMLInfiniteInteger n) {
        //@ assume n != null;
        if (n instanceof JMLFiniteInteger) {
            BigInteger s = val.remainder(((JMLFiniteInteger)n).val);
            //@ assume s != null;
            return new JMLFiniteInteger(s);
        } else if (n.signum() == +1) {
            return this;
        } else {
            return this.negate();
        }
    }

    /** Return this integer modulo the argument.
     */
    public JMLInfiniteInteger mod(JMLInfiniteInteger n)
        throws ArithmeticException {
        //@ assume n != null;
        if (n instanceof JMLFiniteInteger) {
            BigInteger s = val.mod(((JMLFiniteInteger)n).val);
            //@ assume s != null;
            return new JMLFiniteInteger(s);
        } else if (n.signum() == +1) {
            return n;
        } else {
            throw new ArithmeticException("negative divisor for mod");
        }
    }

    /** Return this integer raised to the argument's power.
     */
    public JMLInfiniteInteger pow(int n) {
        BigInteger s = val.pow(n);
        //@ assume s != null;
        return new JMLFiniteInteger(s);
    }

    /** Return this integer approximated by a double.
     */
    public double doubleValue() { return val.doubleValue(); }

    /** Return this integer approximated by a float.
     */
    public float floatValue() { return val.floatValue(); }

    /** Return the decimal representation of this integer.
     */
    public String toString() { return val.toString(); }

    /** Return the digits representing this integer in the given radix.
     */
    public String toString(int radix) { return val.toString(radix); }


    /** Converts this BigInteger to a long
     */
    public long longValue() { return val.longValue(); }

    /** Converts this BigInteger to an integer
     */
    public int intValue() { return val.intValue(); }

}
