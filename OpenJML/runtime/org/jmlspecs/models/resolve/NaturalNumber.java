// @(#)$Id: NaturalNumber.java,v 1.26 2007/06/29 21:01:58 chalin Exp $

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

package org.jmlspecs.models.resolve;

import java.math.BigInteger;

/** The natural numbers.  These are essentially unlimited in size.
 *
 * @version $Revision: 1.26 $
 * @author Gary T. Leavens
 * @see java.math.BigInteger
 * @see org.jmlspecs.models.JMLFiniteInteger
 */
public /*@ pure @*/ class NaturalNumber extends Number
    implements TotallyOrderedCompareTo, org.jmlspecs.models.JMLType
{
    private static final long serialVersionUID = -388120386774993267L;

    /** The value of this natural number. */
    private final /*@ non_null @*/ BigInteger value;
    //@                                      in objectState;

    //@ private constraint_redundantly value == \old(value);
    //@ private invariant value.compareTo(BigInteger.ZERO) >= 0;

    //@ public invariant owner == null;

    /** Initialize this natural number to zero.
     * @see #ZERO
     * @see #NaturalNumber(long)
     * @see #NaturalNumber(BigInteger)
     */
    /*@ public normal_behavior
      @   assignable objectState, owner;
      @   ensures isZero();
      @*/
    public NaturalNumber () {
        //@ set owner = null;
        //@ assume BigInteger.ZERO != null;
        value = BigInteger.ZERO;
    }

    /** Initialize this natural number to the given long value.
     * @see #NaturalNumber()
     * @see #NaturalNumber(BigInteger)
     * @see #valueOf(long)
     */
    /*@ public normal_behavior
      @   requires val >= 0;
      @   assignable objectState, owner;
      @   ensures longValue() == val;
      @*/
    //@ also
    //@    exsures (IllegalArgumentException) val < 0;
    public NaturalNumber (long val)
        throws IllegalArgumentException
    {
        //@ set owner = null;
        if (val >= 0) {
            value = BigInteger.valueOf(val); //@ nowarn NonNull;
        } else {
            throw new IllegalArgumentException();
        }
    }

    /** Initialize this natural number to the given {@link
     * java.math.BigInteger} value.
     * @see #NaturalNumber()
     * @see #NaturalNumber(BigInteger)
     */
    /*@ public normal_behavior
      @   requires val != null && val.compareTo(BigInteger.ZERO) >= 0;
      @   assignable objectState, owner;
      @   ensures bigIntegerValue().equals(val);
      @*/
    public NaturalNumber(/*@ non_null @*/ BigInteger val)
        throws IllegalArgumentException
    {
        //@ set owner = null;
        if (val.compareTo(BigInteger.ZERO) >= 0) {
            value = val;
        } else {
            throw new IllegalArgumentException();
        }
    }

    // Static Factory Methods

    /** Return a natural number with the given value.
     * @see #NaturalNumber(long)
     * @see #NaturalNumber(BigInteger)
     */
    /*@ public normal_behavior
      @   requires val >= 0;
      @   ensures \result != null
      @         && \result.equals(new NaturalNumber(val));
      @*/
    //@ implies_that
    //@    requires val >= 0;
    public static /*@ pure @*/
        /*@ non_null @*/ NaturalNumber valueOf(long val)
    {
        return new NaturalNumber(val);
    }

    /** The natural number zero.
     * @see #NaturalNumber()
     * @see #ONE
     */
    public static final /*@ non_null @*/ NaturalNumber ZERO = valueOf(0);

    /** The natural number one.
     * @see #NaturalNumber(long)
     * @see #valueOf(long)
     * @see #ZERO
     */
    public static final /*@ non_null @*/ NaturalNumber ONE = valueOf(1);

    //@ public invariant ZERO != null && ZERO.equals(valueOf(0));
    //@ public constraint ZERO == \old(ZERO);
    //@ public invariant ONE != null && ONE.equals(valueOf(1));
    //@ public constraint ONE == \old(ONE);

    // Arithmetic Operations

    /** Return the successor of this natural number.
     * @see #suc(NaturalNumber)
     * @see #add
     * @see #ONE
     */
    /*@ public normal_behavior
      @   ensures \result != null && \result.equals(this.add(ONE));
      @*/
    public /*@ non_null @*/ NaturalNumber suc() {
        return add(ONE);
    }

    /** Return the successor of the given natural number.
     * @see #suc()
     * @see #add
     */
    /*@ public normal_behavior
      @   requires v != null;
      @   ensures \result != null && \result.equals(v.suc());
      @   ensures_redundantly \result != null
      @        && \result.equals(v.add(ONE));
      @*/
    public static /*@ pure @*/ /*@ non_null @*/
        NaturalNumber suc(/*@ non_null @*/ NaturalNumber v)
    {
        return v.suc();
    }

    /** Return the sum of this natural number and the given one.
     * @see #suc()
     * @see #add
     */
    /*@ public normal_behavior
      @   requires val != null;
      @   {|
      @      requires val.equals(ZERO);
      @      ensures \result != null && \result.equals(this);
      @   also
      @      forall NaturalNumber v;
      @      requires !(val.equals(ZERO));
      @      ensures v != null && v.suc().equals(val)
      @              ==> \result != null
      @                  && \result.equals(this.add(v).suc());
      @   |}
      @ for_example
      @   public normal_example
      @     requires val != null && val.equals(new NaturalNumber(3))
      @           && this.equals(new NaturalNumber(7));
      @     ensures \result != null && \result.equals(new NaturalNumber(10));
      @*/
    public /*@ non_null @*/
        NaturalNumber add(/*@ non_null @*/ NaturalNumber val)
    {
        return new NaturalNumber(value.add(val.value)); //@ nowarn NonNull;
    } //@ nowarn Exception;

    /** Return the product of this natural number and the given one.
     * @see #divide
     */
    /*@ public normal_behavior
      @   requires val != null;
      @   {|
      @      requires val.equals(ZERO);
      @      ensures \result != null && \result.isZero();
      @   also
      @      forall NaturalNumber v;
      @      requires !(val.equals(ZERO));
      @      ensures v != null && v.suc().equals(val)
      @              ==> \result != null
      @                  && \result.equals(this.add(this.multiply(v)));
      @    |}
      @ implies_that
      @   public normal_behavior
      @     requires val != null && val.equals(ONE);
      @     ensures \result != null && \result.equals(this);
      @ for_example
      @   public normal_example
      @     requires val != null && val.equals(new NaturalNumber(3))
      @           && this.equals(new NaturalNumber(7));
      @     ensures \result != null && \result.equals(new NaturalNumber(21));
      @*/
    public /*@ non_null @*/ 
        NaturalNumber multiply(/*@ non_null @*/ NaturalNumber val)
    {
        return new NaturalNumber(value.multiply(val.value));//@ nowarn NonNull;
    } //@ nowarn Exception;

    /** Return the quotient of this natural number divided by the given one.
     * @see #multiply
     */
    /*@   public normal_behavior
      @     forall NaturalNumber quot, rem;
      @     requires val != null && !val.equals(ZERO);
      @     ensures quot != null && rem != null && rem.compareTo(this) < 0
      @                && this.equals(rem.add(quot.multiply(val)))
      @             ==> \result.equals(quot);
      @ also
      @   public exceptional_behavior
      @     requires val != null && val.equals(ZERO);
      @     signals_only ArithmeticException;
      @ implies_that
      @   public normal_behavior
      @     requires val != null && val.equals(ONE);
      @     ensures \result != null && \result.equals(this);
      @ for_example
      @   public normal_example
      @     requires val != null && val.equals(new NaturalNumber(3))
      @           && this.equals(new NaturalNumber(22));
      @     ensures \result != null && \result.equals(new NaturalNumber(7));
      @*/
    public /*@ non_null @*/ 
        NaturalNumber divide(/*@ non_null @*/ NaturalNumber val)
    {
        return new NaturalNumber(value.divide(val.value)); //@ nowarn NonNull;
    } //@ nowarn Exception;

    /** Return the remainder of this natural number divided by the given one.
     * @see #divide
     */
    /*@   public normal_behavior
      @     forall NaturalNumber quot, rem;
      @     requires val != null && !val.equals(ZERO);
      @     ensures quot != null && rem != null && rem.compareTo(this) < 0
      @                && this.equals(rem.add(quot.multiply(val)))
      @             ==> \result.equals(rem);
      @ also
      @   public exceptional_behavior
      @     requires val != null && val.equals(ZERO);
      @     signals_only ArithmeticException;
      @ implies_that
      @   public normal_behavior
      @     requires val != null && val.equals(ONE);
      @     ensures \result != null && \result.equals(ZERO);
      @ for_example
      @   public normal_example
      @     requires val != null && val.equals(new NaturalNumber(3))
      @           && this.equals(new NaturalNumber(22));
      @     ensures \result != null && \result.equals(new NaturalNumber(1));
      @*/
    public /*@ non_null @*/ 
        NaturalNumber remainder(/*@ non_null @*/ NaturalNumber val)
    {
        return new NaturalNumber(value.remainder(val.value));//@ nowarn NonNull;
    } //@ nowarn Exception;

    /** Return this natural number multiplied by itself the given
     * number of times.
     * @see #multiply
     * @see #pow(int)
     */
    /*@ public normal_behavior
      @   requires exponent != null;
      @   {|
      @      requires !isZero() && exponent.equals(ZERO);
      @      ensures \result != null && \result.equals(ONE);
      @   also
      @      forall NaturalNumber v;
      @      requires !(exponent.equals(ZERO))
      @            && exponent.compareTo(BigInteger.valueOf(Integer.MAX_VALUE))
      @                     <= 0;
      @      ensures v != null && v.suc().equals(exponent)
      @              ==> \result != null
      @                  && \result.equals(this.multiply(this.pow(v)));
      @   |}
      @ implies_that
      @   public normal_behavior
      @     requires exponent != null && exponent.equals(ONE);
      @     ensures \result != null && \result.equals(this);
      @ also
      @   public normal_behavior
      @     requires exponent != null && this.isZero() && !exponent.isZero()
      @            && exponent.compareTo(BigInteger.valueOf(Integer.MAX_VALUE))
      @                     <= 0;
      @     ensures \result != null && \result.equals(ZERO);
      @     ensures_redundantly \result != null && \result.equals(this);
      @ for_example
      @   public normal_example
      @     requires exponent != null && exponent.equals(new NaturalNumber(3))
      @           && this.equals(new NaturalNumber(3));
      @     ensures \result != null && \result.equals(new NaturalNumber(27));
      @*/
    public /*@ non_null @*/
        NaturalNumber pow(/*@ non_null @*/ NaturalNumber exponent)
        throws OutOfMemoryError
    {
        if (exponent.compareTo(intMaxVal) > 0) {
            throw new OutOfMemoryError();
        } else {
            return new NaturalNumber(value.pow(exponent.value.intValue()));//@ nowarn NonNull;
        }
    } //@ nowarn Exception;

    /** The maximum integer as a natural number.
     */
    private static final /*@ non_null @*/ NaturalNumber intMaxVal
        = new NaturalNumber(Integer.MAX_VALUE);

    /** Return this natural number multiplied by itself the given
     * number of times.
     * @see #multiply
     * @see #pow(NaturalNumber)
     */
    /*@ public normal_behavior
      @   requires exponent >= 0;
      @   {|
      @      requires !isZero() && exponent == 0;
      @      ensures \result != null && \result.equals(ONE);
      @   also
      @      forall int v;
      @      requires exponent != 0;
      @      ensures v+1 == exponent
      @              ==> \result != null
      @                  && \result.equals(this.multiply(this.pow(v)));
      @   |}
      @ implies_that
      @   public normal_behavior
      @     requires exponent == 1;
      @     ensures \result != null && \result.equals(this);
      @*/
    public /*@ non_null @*/ NaturalNumber pow(int exponent) {
        return new NaturalNumber(value.pow(exponent));//@ nowarn NonNull;
    } //@ nowarn Exception;

    /** Return the greatest common denominator of this number and the
     * given number.
     */
    /*@   public normal_behavior
      @     forall NaturalNumber n;
      @     requires !this.isZero() && val != null && !val.isZero();
      @     ensures n != null && n.divides(this) && n.divides(val)
      @             && (\forall NaturalNumber m;
      @                         m != null && m.divides(this) && m.divides(val);
      @                         n.compareTo(m) >= 0)
      @             ==> \result.equals(n);
      @ also
      @   public normal_behavior
      @     requires this.isZero() && val != null && val.isZero();
      @     ensures \result.isZero();
      @ for_example
      @   public normal_example
      @     requires val != null && val.equals(new NaturalNumber(12))
      @           && this.equals(new NaturalNumber(30));
      @     ensures \result != null && \result.equals(new NaturalNumber(6));
      @*/
    public /*@ non_null @*/ 
        NaturalNumber gcd(/*@ non_null @*/ NaturalNumber val)
    {
        return new NaturalNumber(value.gcd(val.value)); //@ nowarn NonNull;
    } //@ nowarn Exception;

    // Modular Arithmetic Operations

    /** Return this natural number modulo the given one.
     * @see #remainder
     */
    /*@ public normal_behavior
      @   requires m != null && !m.isZero();
      @   ensures \result.equals(this.remainder(m));
      @ also
      @   public exceptional_behavior
      @     requires m != null && m.equals(ZERO);
      @     signals_only ArithmeticException;
      @*/
    public /*@ non_null @*/ 
        NaturalNumber mod(/*@ non_null @*/ NaturalNumber m)
    {
        return new NaturalNumber(value.mod(m.value)); //@ nowarn NonNull;
    } //@ nowarn Exception;

    // Shift Operations

    /** Return this natural number left shifted the given number of bits.
     * @see #shiftRight(int)
     * @see #pow(int)
     */
    /*@   public normal_behavior
      @     requires n >= 0;
      @     ensures \result != null
      @        && \result.equals(this.multiply(
      @                  new NaturalNumber(2).pow(new NaturalNumber(n))));
      @ also
      @   public normal_behavior
      @     requires n <= 0;
      @     ensures \result != null
      @        && \result.equals(this.shiftRight(Math.abs(n)));
      @ implies_that
      @   public normal_behavior
      @     requires n == 0;
      @     ensures \result != null && \result.equals(this);
      @*/
    public /*@ non_null @*/ NaturalNumber shiftLeft(int n) {
        return new NaturalNumber(value.shiftLeft(n)); //@ nowarn NonNull;
    } //@ nowarn Exception;

    /** Return this natural number right shifted the given number of bits.
     * @see #shiftLeft(int)
     * @see #pow(int)
     */
    /*@   public normal_behavior
      @     requires n >= 0;
      @     ensures \result != null
      @        && \result.equals(this.divide(
      @                  new NaturalNumber(2).pow(new NaturalNumber(n))));
      @ also
      @   public normal_behavior
      @     requires n <= 0;
      @     ensures \result != null
      @        && \result.equals(this.shiftLeft(Math.abs(n)));
      @*/
    public /*@ non_null @*/ NaturalNumber shiftRight(int n) {
        return new NaturalNumber(value.shiftRight(n)); //@ nowarn NonNull;
    } //@ nowarn Exception;

    // Comparison Operations

    /** Return negative if this natural numbers strictly less than the
     * given one, 0 if they are equal, and positive if this natural
     * numbers is strictly greater than the given one.
     * @see #compareTo(Object)
     * @see #equals
     */
    /*@ public normal_behavior
      @   requires val != null;
      @   ensures \result
      @            == bigIntegerValue().compareTo(val.bigIntegerValue());
      @*/
    public int compareTo(/*@ non_null @*/ NaturalNumber val) {
        return value.compareTo(val.value);
    }

    /*@ public normal_behavior
      @   ensures \result == bigIntegerValue().compareTo(val);
      @*/
    public int compareTo(/*@ non_null @*/ BigInteger val) {
        return value.compareTo(val);
    }

    /*@ also
      @   public normal_behavior
      @     requires o != null && o instanceof NaturalNumber;
      @     requires this.equals(o);
      @     ensures \result == 0;
      @*/  
    public int compareTo(/*@ non_null @*/ Object o)
           throws ClassCastException {
        return value.compareTo(((NaturalNumber)o).value); //@ nowarn Cast;
    }

    /** Tell if this object is equal to the given argument.
     * @see #compareTo(Object)
     * @see #compareTo(NaturalNumber)
     * @see #equals
     */
    public boolean equals(/*@ nullable @*/ Object x) {
        if (x == null || !(x instanceof NaturalNumber)) {
            return false;
        } else {
            return value.equals(((NaturalNumber)x).value);
        }
    }

    public Object clone() {
        return this;
    }

    /** Tell if this object is equal to zero.
     * @see #ZERO
     * @see #compareTo(NaturalNumber)
     * @see #equals
     */
    /*@ public normal_behavior
      @   ensures \result <==> this.equals(ZERO);
      @   ensures_redundantly \result <==> this.compareTo(ZERO) == 0;
      @   ensures_redundantly \result <==> this.equals(new NaturalNumber());
      @*/
    public boolean isZero() {
        return value.equals(BigInteger.ZERO);
    }

    /** Tell if this natural number divides the given one evenly.
     * @see #remainder
     * @see #mod
     */
    /*@ public normal_behavior
      @   requires val != null;
      @   ensures \result <==> !isZero() && val.remainder(this).equals(ZERO);
      @*/
    public boolean divides(/*@ non_null @*/ NaturalNumber val) {
        return !isZero() && val.remainder(this).equals(ZERO);
    }

    /** Return the smaller of the given natural number and this one.
     * @see #max
     * @see #compareTo(NaturalNumber)
     */
    /*@ public normal_behavior
      @   requires val != null;
      @   {|
      @      requires this.compareTo(val) <= 0;
      @      ensures \result != null && \result.equals(this);
      @   also
      @      requires val.compareTo(this) <= 0;
      @      ensures \result != null && \result.equals(val);
      @   |}
      @*/
    public NaturalNumber min(/*@ non_null @*/ NaturalNumber val) {
        return new NaturalNumber(value.min(val.value)); //@ nowarn NonNull;
    } //@ nowarn Exception;

    /** Return the smaller of the given natural number and this one.
     * @see #max
     * @see #compareTo(NaturalNumber)
     */
    /*@ public normal_behavior
      @   requires val != null;
      @   {|
      @      requires this.compareTo(val) >= 0;
      @      ensures \result != null && \result.equals(this);
      @   also
      @      requires val.compareTo(this) >= 0;
      @      ensures \result != null && \result.equals(val);
      @   |}
      @*/
    public NaturalNumber max(/*@ non_null @*/ NaturalNumber val) {
        return new NaturalNumber(value.max(val.value)); //@ nowarn NonNull;
    } //@ nowarn Exception;

    // Hash Function

    // inherit specification and documentation comment
    public int hashCode() {
        return value.hashCode();
    }

    // inherit specification and documentation comment
    public String toString() {
        return value.toString();
    }

    /** Return the BigInteger value of this natural number.
     * @see #intValue
     * @see #longValue
     */
    /*@ public normal_behavior
      @   ensures \result != null
      @        && new NaturalNumber(\result).equals(this);
      @*/
    public /*@ non_null @*/ BigInteger bigIntegerValue() {
        return value;
    }

    // overrides of some of Number's methods

    // inherit specification and documentation comment
    public int intValue() {
        return value.intValue();
    }

    // inherit specification and documentation comment
    public long longValue() {
        return value.longValue();
    }

    // inherit specification and documentation comment
    public float floatValue()  {
        return value.floatValue();
    }

    // inherit specification and documentation comment
    public double doubleValue() {
        return value.doubleValue();
    }
}
