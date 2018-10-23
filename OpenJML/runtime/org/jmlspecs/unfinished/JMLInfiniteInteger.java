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


package org.jmlspecs.unfinished;

import java.math.BigInteger;
import org.jmlspecs.annotation.*;

/** Infinite precision integers with an plus and minus infinity.
 *
 * <p>This type is intended to support reasoning like that done by
 * Eric Hehner for the time behavior of programs.  Of course, it could
 * also be used for other purposes as well.
 *
 * @author Gary T. Leavens, David R. Cok
 * @see java.math.BigInteger
 */
//+OPENJML@ immutable
public @Pure interface JMLInfiniteInteger
    extends JMLComparable<JMLInfiniteInteger>
{
    /** Does this object represent a nonnegative integer? */
    //@ public model instance boolean nonnegative;

    /** The sign of this integer. */
    //@ public model instance int sign; in nonnegative;
    //@ public invariant sign == -1 || sign == 0 || sign == +1;

    //@ public instance represents nonnegative <- sign >= 0;

    /** Is this integer infinite? */
    //@ public model instance boolean is_infinite;

    /** If this integer is not infinite, its finite value. */
    //@ public model instance BigInteger finite_value;

    /*@ public instance invariant sign == -1 || sign == 0 || sign == +1;
      @ public instance invariant
      @            !is_infinite ==> finite_value != null
      @                             && sign == finite_value.signum();
      @*/
    /*@ public instance invariant_redundantly
      @  sign == 0 <==> !is_infinite
      @                 && finite_value.equals(BigInteger.ZERO);
      @*/

    //@ public instance constraint nonnegative == \old(nonnegative);
    //@ public instance constraint sign == \old(sign);
    //@ public instance constraint is_infinite == \old(is_infinite);
    //@ public instance constraint finite_value == \old(finite_value);

    /** Return the sign of this integer.
     */
    /*@ public normal_behavior
      @     ensures \result == sign;
      @ implies_that
      @   public normal_behavior
      @     ensures \result == -1 || \result == 0 || \result == +1;
      @     ensures (\result == 0 || \result == +1) <==> nonnegative;
      @     ensures \result == -1 <==> !nonnegative;
      @*/
    int signum();

    /** Tell if this integer is finite.
     */
    /*@ public normal_behavior
      @   ensures \result == !is_infinite;
      @*/
    boolean isFinite();

    /** Assuming this integer is finite, return its value.
     */
    /*@  public normal_behavior
      @     requires !is_infinite;
      @     ensures \result != null && \result.equals(finite_value);
      @  also
      @   public exceptional_behavior
      @     requires is_infinite;
      @     signals_only ArithmeticException;
      @*/
    @NonNull BigInteger finiteValue() throws ArithmeticException;

    /** Compare this to o, returning a comparison code.
     *  @param o the object this is compared to.
     *  @exception ClassCastException when o is not
     *             a JMLInfiniteInteger or a BigInteger.
     * @see #equals(Object)
     * @see #greaterThanOrEqualTo
     * @see #greaterThan
     * @see #lessThanOrEqualTo
     * @see #lessThan
     */
    /*@ also
      @   public normal_behavior
      @     requires o != null && o instanceof JMLInfiniteInteger;
      @     {|
      @        old JMLInfiniteInteger n = (JMLInfiniteInteger)o;
      @        {|
      @           requires lessThan(n);
      @           ensures \result == -1;
      @          also
      @           requires equals(n);
      @           ensures \result == 0;
      @          also
      @           requires greaterThan(n);
      @           ensures \result == +1;
      @        |}
      @     |}
      @ also
      @   public normal_behavior
      @     requires o != null && o instanceof BigInteger;
      @     {|
      @         requires is_infinite && !nonnegative;
      @         ensures \result == -1;
      @        also
      @         requires !is_infinite;
      @         ensures \result == finite_value.compareTo((BigInteger)o);
      @        also
      @         requires is_infinite && nonnegative;
      @         ensures \result == +1;
      @     |}
      @ also
      @   public exceptional_behavior
      @     requires o != null 
      @          && !(o instanceof JMLInfiniteInteger)
      @          && !(o instanceof BigInteger);
      @     signals_only ClassCastException;
      @*/
    int compareTo(@NonNull JMLInfiniteInteger o) throws ClassCastException;

    /** Tell whether this integer is equal to the argument.
     ** Note that comparisons to BigIntegers are also handled.
     * @see #compareTo(Object)
     * @see #greaterThanOrEqualTo
     * @see #greaterThan
     * @see #lessThanOrEqualTo
     * @see #lessThan
     */
    /*@ also
      @   public normal_behavior
      @     requires o != null && o instanceof JMLInfiniteInteger;
      @     {|
      @        old JMLInfiniteInteger n = (JMLInfiniteInteger)o;
      @        ensures \result <==>
      @                   sign == n.sign
      @                && is_infinite == n.is_infinite
      @                && (!is_infinite && !n.is_infinite
      @                    ==> finite_value.compareTo(n.finite_value) == 0);
      @     |}
      @ also
      @   public normal_behavior
      @     requires o != null && o instanceof BigInteger;
      @     {|
      @        old BigInteger bi = (BigInteger)o;
      @        ensures \result <==>
      @                !is_infinite && finite_value.compareTo(bi) == 0;
      @     |}
      @ also
      @   public normal_behavior
      @     requires o == null
      @       || !(o instanceof BigInteger || o instanceof JMLInfiniteInteger);
      @     ensures !\result;
      @*/
    boolean equals(@Nullable Object o);

    /** Tell if this integer is greater than or equal to the argument.
     * @see #equals(Object)
     * @see #compareTo(Object)
     * @see #greaterThan
     * @see #lessThanOrEqualTo
     * @see #lessThan
     */
    /*@  public normal_behavior
      @     requires n != null;
      @     ensures \result <==>
      @           (is_infinite ==>
      @                 (nonnegative || (!n.nonnegative && n.is_infinite)))
      @        && (!is_infinite
      @                ==> ((n.is_infinite && !n.nonnegative)
      @                     || finite_value.compareTo(n.finite_value) >= 0));
      @ implies_that
      @   public normal_behavior
      @      requires n != null;
      @      {|
      @         requires (nonnegative && is_infinite)
      @               || (!n.nonnegative && n.is_infinite);
      @         ensures \result;
      @       also
      @         requires (n.nonnegative && n.is_infinite)
      @               || (!nonnegative && is_infinite);
      @         ensures !\result;
      @       also
      @         requires !is_infinite && !n.is_infinite;
      @         ensures \result <==>
      @                   finite_value.compareTo(n.finite_value) >= 0;
      @      |}
      @*/
    boolean greaterThanOrEqualTo(@NonNull JMLInfiniteInteger n);

    /** Tell if this integer is less than or equal to the argument.
     * @see #equals(Object)
     * @see #compareTo(Object)
     * @see #greaterThanOrEqualTo
     * @see #greaterThan
     * @see #lessThan
     */
    /*@   public normal_behavior
      @      requires n != null;
      @      ensures \result <==> n.greaterThanOrEqualTo(this);
      @*/
    boolean lessThanOrEqualTo(@NonNull JMLInfiniteInteger n);

    /** Tell if this integer is strictly greater than the argument.
     * @see #equals(Object)
     * @see #compareTo(Object)
     * @see #greaterThanOrEqualTo
     * @see #lessThanOrEqualTo
     * @see #lessThan
     */
    /*@   public normal_behavior
      @      requires n != null;
      @      ensures \result <==> !equals(n) && greaterThanOrEqualTo(n);
      @*/
    boolean greaterThan(@NonNull JMLInfiniteInteger n);

    /** Tell if this integer is strictly less than the argument.
     * @see #equals(Object)
     * @see #compareTo(Object)
     * @see #greaterThanOrEqualTo
     * @see #greaterThan
     * @see #lessThanOrEqualTo
     */
    /*@   public normal_behavior
      @      requires n != null;
      @      ensures \result <==> !equals(n) && lessThanOrEqualTo(n);
      @*/
    boolean lessThan(@NonNull JMLInfiniteInteger n);

    /** Return a hash code for this integer.
     */
    int hashCode();

    /** Return the absolute value of this integer.
     * @see #negate
     */
    /*@ public normal_behavior
      @   ensures \result != null && \result.nonnegative
      @        && \result.is_infinite == is_infinite
      @        && (!\result.is_infinite
      @            ==> \result.finite_value.equals(finite_value.abs()));
      @*/
    @NonNull JMLInfiniteInteger abs();

    /** Return the maximum of this integer and the argument.
     * @see #min
     */
    /*@ public normal_behavior
      @   requires n != null;
      @   {|
      @      requires this.greaterThanOrEqualTo(n);
      @      ensures \result.equals(this);
      @    also
      @      requires n.greaterThanOrEqualTo(this);
      @      ensures \result.equals(n);
      @   |}
      @*/
    @NonNull JMLInfiniteInteger
        max(@NonNull JMLInfiniteInteger n);

    /** Return the minimum of this integer and the argument.
     * @see #max
     */
    /*@ public normal_behavior
      @   requires n != null;
      @   {|
      @      requires this.lessThanOrEqualTo(n);
      @      ensures \result.equals(this);
      @    also
      @      requires n.lessThanOrEqualTo(this);
      @      ensures \result.equals(n);
      @   |}
      @*/
    @NonNull JMLInfiniteInteger
        min(@NonNull JMLInfiniteInteger n);

    /** Return the negation of this integer.
     * @see #abs
     * @see #subtract
     */
    /*@ public normal_behavior
      @   ensures \result != null && \result.sign == -1 * sign;
      @  also
      @   requires is_infinite;
      @   ensures \result.is_infinite;
      @  also
      @   requires !is_infinite;
      @   ensures !\result.is_infinite
      @        && \result.finite_value.equals(finite_value.negate());
      @*/
    @NonNull JMLInfiniteInteger negate();

    /** Return the sum of this integer and the argument.
     * @see #subtract
     */
    /*@ public normal_behavior
      @   requires n != null;
      @   {|
      @      ensures \result != null;
      @    also
      @      requires is_infinite && !n.is_infinite;
      @      ensures \result.equals(this);
      @    also
      @      requires !is_infinite && n.is_infinite;
      @      ensures \result.equals(n);
      @    also
      @      requires is_infinite && n.is_infinite;
      @      {|
      @         requires nonnegative == n.nonnegative;
      @         ensures \result.equals(this);
      @       also
      @         requires nonnegative != n.nonnegative;
      @         ensures \result.equals(new BigInteger("0"));
      @      |}
      @    also
      @      requires !is_infinite && !n.is_infinite;
      @      ensures !\result.is_infinite
      @       && \result.finite_value.equals(finite_value.add(n.finite_value));
      @   |}
      @*/
    @NonNull JMLInfiniteInteger
        add(@NonNull JMLInfiniteInteger n);

    /** Return the difference between this integer and the argument.
     * @see #add
     * @see #negate
     */
    /*@ public normal_behavior
      @   requires n != null;
      @   {|
      @      ensures \result != null;
      @    also
      @      requires is_infinite && !n.is_infinite;
      @      ensures \result.equals(this);
      @    also
      @      requires !is_infinite && n.is_infinite;
      @      ensures \result.equals(n.negate());
      @    also
      @      requires is_infinite && n.is_infinite;
      @      {|
      @         requires nonnegative == n.nonnegative;
      @         ensures \result.equals(new BigInteger("0"));
      @       also
      @         requires nonnegative != n.nonnegative;
      @         ensures \result.equals(this);
      @      |}
      @    also
      @      requires !is_infinite && !n.is_infinite;
      @      ensures !\result.is_infinite
      @       && \result.finite_value.equals(finite_value.subtract(n.finite_value));
      @   |}
      @*/
    @NonNull JMLInfiniteInteger
        subtract(@NonNull JMLInfiniteInteger n);

    /** Return the product of this integer and the argument.
     * @see #divide
     * @see #remainder
     * @see #mod
     */
    /*@ public normal_behavior
      @   requires n != null;
      @   {|
      @      ensures \result != null && \result.sign == sign * n.sign;
      @    also
      @      requires equals(new BigInteger("0"))
      @               || n.equals(new BigInteger("0"));
      @      ensures \result.equals(new BigInteger("0"));
      @    also
      @      requires !(equals(new BigInteger("0"))
      @                 || n.equals(new BigInteger("0")));
      @      {|
      @         requires is_infinite || n.is_infinite;
      @         ensures \result.is_infinite;
      @       also
      @         requires !is_infinite && !n.is_infinite;
      @         ensures !\result.is_infinite
      @           && \result.finite_value.equals(finite_value.multiply(n.finite_value));
      @      |}
      @   |}
      @*/
    @NonNull JMLInfiniteInteger
        multiply(@NonNull JMLInfiniteInteger n);

    /** Return the quotient of this integer divided by the argument.
     * @see #multiply
     * @see #remainder
     * @see #mod
     */
    /*@ public normal_behavior
      @   requires n != null && n.sign != 0;
      @   {|
      @      ensures \result != null
      @           && (\result.sign == 0|| \result.sign == sign * n.sign);
      @    also
      @      requires is_infinite && n.is_infinite;
      @      ensures !\result.is_infinite
      @           && \result.abs().equals(new BigInteger("1"));
      @    also
      @      requires is_infinite && !n.is_infinite;
      @      ensures \result.is_infinite;
      @    also
      @      requires !is_infinite && n.is_infinite;
      @      ensures \result.equals(new BigInteger("0"));
      @    also
      @      requires !is_infinite && !n.is_infinite;
      @      ensures !\result.is_infinite
      @       && \result.finite_value.equals(finite_value.divide(n.finite_value));
      @   |}
      @ also
      @   public exceptional_behavior
      @     requires n != null && n.sign == 0;
      @     signals_only ArithmeticException;
      @*/
    @NonNull JMLInfiniteInteger
        divide(@NonNull JMLInfiniteInteger n)
        throws ArithmeticException;

    /** Return the remainder of this integer divided by the argument.
     * @see #divide
     * @see #mod
     */
    /*@ public normal_behavior
      @   requires n != null && n.sign != 0;
      @   {|
      @      ensures \result != null;
      @    also
      @      requires is_infinite;
      @      ensures \result.equals(new BigInteger("0"));
      @    also
      @      requires !is_infinite && n.is_infinite;
      @      ensures \result.abs().equals(this.abs());
      @      ensures \result.sign == sign * n.sign;
      @    also
      @      requires !is_infinite && !n.is_infinite;
      @      ensures !\result.is_infinite
      @       && \result.finite_value
      @                 .equals(finite_value.remainder(n.finite_value));
      @   |}
      @ also
      @   public exceptional_behavior
      @     requires n != null && n.sign == 0;
      @     signals_only ArithmeticException;
      @*/
    @NonNull JMLInfiniteInteger
        remainder(@NonNull JMLInfiniteInteger n)
        throws ArithmeticException;

    /** Return this integer modulo the argument.
     * @see #divide
     * @see #remainder
     */
    /*@ public normal_behavior
      @   requires n != null && n.sign == +1;
      @   {|
      @      ensures \result != null && \result.sign >= 0;
      @    also
      @      requires is_infinite;
      @      ensures \result.equals(new BigInteger("0"));
      @    also
      @      requires !is_infinite && n.is_infinite;
      @      ensures \result.equals(n);
      @    also
      @      requires !is_infinite && !n.is_infinite;
      @      ensures !\result.is_infinite
      @       && \result.finite_value.equals(finite_value.mod(n.finite_value));
      @   |}
      @ also
      @   public exceptional_behavior
      @     requires n != null && n.sign != +1;
      @     signals_only ArithmeticException;
      @*/
    @NonNull JMLInfiniteInteger
        mod(@NonNull JMLInfiniteInteger n)
        throws ArithmeticException;

    /** Return this integer raised to the argument's power.
     */
    /*@ public normal_behavior
      @   requires n >= 0;
      @   {|
      @      ensures \result != null
      @           && (\result.nonnegative <==> n % 2 == 0 || nonnegative);
      @    also
      @      requires is_infinite;
      @      ensures n != 0 ==> \result.is_infinite;
      @      ensures n == 0
      @          ==> !\result.is_infinite
      @              && \result.finite_value.equals(new BigInteger("1"));
      @    also
      @      requires !is_infinite;
      @      ensures !\result.is_infinite
      @           && \result.finite_value.equals(finite_value.pow(n));
      @   |}
      @ also
      @   public exceptional_behavior
      @     requires n < 0;
      @     signals_only ArithmeticException;
      @*/
    @NonNull JMLInfiniteInteger pow(int n) throws ArithmeticException;

    /** Return this integer approximated by a double.
     * @see #floatValue
     */
    /*@ public normal_behavior
      @    requires is_infinite && nonnegative;
      @    ensures \result == Double.POSITIVE_INFINITY;
      @  also
      @    requires is_infinite && !nonnegative;
      @    ensures \result == Double.NEGATIVE_INFINITY;
      @  also
      @    requires !is_infinite;
      @    ensures \result == finite_value.doubleValue();
      @*/
    double doubleValue();

    /** Return this integer approximated by a float.
     * @see #doubleValue
     */
    /*@ public normal_behavior
      @    requires is_infinite && nonnegative;
      @    ensures \result == Float.POSITIVE_INFINITY;
      @  also
      @    requires is_infinite && !nonnegative;
      @    ensures \result == Float.NEGATIVE_INFINITY;
      @  also
      @    requires !is_infinite;
      @    ensures \result == finite_value.floatValue();
      @*/
    float floatValue();

    /** Return the decimal representation of this integer.
     * @see #toString(int)
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result.equals(toString(10));
      @*/
    @NonNull String toString();

    /** Return the digits representing this integer in the given radix.
     * @see #toString()
     */
    @NonNull String toString(int radix)
        /*@ public model_program {
          @    if (is_infinite) {
          @       if (nonnegative) {
          @         return "Infinity";
          @       } else {
          @         return "-Infinity";
          @       }
          @    } else {
          @      return finite_value.toString(radix);
          @    }
          @ }
          @*/
        ;
}
