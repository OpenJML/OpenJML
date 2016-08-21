// @(#)$Id: JMLMath.java,v 1.5 2005/07/07 21:03:07 leavens Exp $

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
import java.lang.Math; // FIXME - Necessary to avoid a warning that the link to java.lang.Math cannot be found.

/** A JML class that implements methods equivalent to those available in
 * {@link java.lang.Math} but that are defined over <code>\bigint</code> and
 * <code>\real</code> instead.
 *
 * @version $Revision: 1.5 $
 * @author Patrice Chalin
 * @see java.lang.Math
 * <!--see JMLBigint-->
 * <!--see JMLReal-->
 */
//-@ immutable
public /*@ pure @*/ final strictfp class JMLMath {

    /**
     * Don't let anyone instantiate this class.
     */
    private JMLMath() {}

    /**
     * The <code>\real</code> value that is closer than any other to
     * <i>e</i>, the base of the natural logarithms. !FIXME! define exactly.
     */
    // -- @ public static final \real E;
    // error: Final field "E" may not have been initialized [JLS2 8.3.1.2]

    /**
     * The <code>\real</code> value that is closer than any other to
     * <i>pi</i>, the ratio of the circumference of a circle to its
     * diameter. !FIXME! define exactly.
     */
    // -- @ public static final \real PI;

    // Trig functions, etc.

    /**
     * Returns the correctly rounded positive square root of a 
     * <code>\real</code> value.
     * 
     * @param   a   a value.
     * <!--@return  the value of &radic;&nbsp;<code>a</code>.-->
     * @return  the positive square root of <code>a</code>.
     */
    /*@
      @ public normal_behavior
      @  ensures \result > 0 && \result * \result == a;
      @*/
    //@ model public static pure \real sqrt(\real a);

    /**
     * Returns the smallest (closest to negative infinity) 
     * <code>\real</code> value that is not less than the argument and is 
     * equal to a mathematical integer. 
     *
     * @param   a   a value.
     * <!--@return  the value &lceil;&nbsp;<code>a</code>&nbsp;&rceil;.-->
     * @return  the smallest (closest to negative infinity) 
     *          <code>\real</code> value that is not less than the argument
     *          and is equal to a mathematical integer. 
     */
    /*@
      @ public normal_behavior
      @  ensures (* \result == TBC *);
      @*/
    //@ model public static pure \real ceil(\real a);

    /**
     * Returns the largest (closest to positive infinity) 
     * <code>\real</code> value that is not greater than the argument and 
     * is equal to a mathematical integer. 
     *
     * @param   a   a value.
     * <!--@return  the value &lfloor;&nbsp;<code>a</code>&nbsp;&rfloor;.-->
     * @return  the largest (closest to positive infinity) 
     *          <code>\real</code> value that is not greater than the argument
     *          and is equal to a mathematical integer. 
     */
    /*@
      @ public normal_behavior
      @  ensures (* \result == TBC *);
      @*/
    //@ model public static pure \real floor(\real a);

    /**
     * Returns the <code>\real</code> value that is closest in value
     * to the argument and is equal to a mathematical integer. If two
     * <code>\real</code> values that are mathematical integers are
     * equally close, the result is the integer value that is
     * even. 
     *
     * @param   a   a <code>\real</code> value.
     * @return  the closest <code>\real</code> value to <code>a</code> that is
     *          equal to a mathematical integer.
     */
    /*@
      @ public normal_behavior
      @  ensures \result == nearestInteger(a);
      @*/
    //@ model public static pure \real rint(\real a);

    /*@
      @ public normal_behavior
      @  ensures abs(\result - a) <= 0.5 &&
      @          abs(\result - a) == 0.5 ==> \result % 2 == 0;
      @*/
    //@ model public static pure \bigint nearestInteger(\real a);

    // atan2 - TBC.

    /**
     * Returns of value of the first argument raised to the power of the
     * second argument.
     *
     * @param   a   the base.
     * @param   b   the exponent.
     * @return  the value <code>a<sup>b</sup></code>.
     */
    /*@
      @ public normal_behavior
      @  ensures (* \result == TBC *);
      @*/
    //@ model public static pure \real pow(\real a, \real b);

    /**
     * Returns the closest <code>\bigint</code> to the argument. The result is
     * equal to the value of the expression:
     * <p><pre>JMLMath.floor(a + 0.5d)</pre>
     *
     * @param   a   a <code>\real</code> value.
     * @return  the value of the argument rounded to the nearest
     *          <code>\bigint</code> value, i.e. <pre>JMLMath.floor(a + 0.5d)</pre>.
     */
    /*@
      @ public normal_behavior
      @  ensures \result == (\bigint)floor(a + 0.5d);
      @
      @ model public static pure \bigint round(\real a) {
      @   return (\bigint)floor(a + 0.5d);
      @ }
      @*/

    // Random number gen ... TBC.

    /**
     * Returns the absolute value of a <code>\bigint</code> value.
     * If the argument is not negative, the argument is returned.
     * If the argument is negative, the negation of the argument is returned. 
     *
     * @param   a   the argument whose absolute value is to be determined
     * @return  the absolute value of the argument.
     */
    /*@
      @ public normal_behavior
      @  ensures \result == ((a < 0) ? -a : a);
      @
      @ model public static pure \bigint abs(\bigint a) {
      @   return (a < 0) ? -a : a;
      @ }
      @*/

    /**
     * Returns the absolute value of a <code>\real</code> value.
     * If the argument is not negative, the argument is returned.
     * If the argument is negative, the negation of the argument is returned.
     *
     * @param   a   the argument whose absolute value is to be determined
     * @return  the absolute value of the argument.
     */
    /*@
      @ public normal_behavior
      @  ensures \result == ((a < 0) ? - a : a);
      @
      @ model public static pure \real abs(\real a) {
      @   return (a < 0) ? - a : a;
      @ }
      @*/

    /**
     * Returns the greater of two <code>\bigint</code> values.
     *
     * @param   a   an argument.
     * @param   b   another argument.
     * @return  the larger of <code>a</code> and <code>b</code>.
     */
    /*@
      @ public normal_behavior
      @  ensures \result == ((a >= b) ? a : b);
      @
      @ model public static pure \bigint max(\bigint a, \bigint b) {
      @   return (a >= b) ? a : b;
      @ }
      @*/

    /**
     * Returns the greater of two <code>\real</code> values.
     *
     * @param   a   an argument.
     * @param   b   another argument.
     * @return  the larger of <code>a</code> and <code>b</code>.
     */
    /*@
      @ public normal_behavior
      @  ensures \result == ((a >= b) ? a : b);
      @
      @ model public static pure \real max(\real a, \real b) {
      @   return (a >= b) ? a : b;
      @ }
      @*/

    /**
     * Returns the smaller of two <code>int</code> values.
     *
     * @param   a   an argument.
     * @param   b   another argument.
     * @return  the smaller of <code>a</code> and <code>b</code>.
     */
    /*@
      @ public normal_behavior
      @  ensures \result == ((a <= b) ? a : b);
      @
      @ model public static pure \bigint min(\bigint a, \bigint b) {
      @   return (a <= b) ? a : b;
      @ }
      @*/

    /**
     * Returns the smaller of two <code>\real</code> values.
     *
     * @param   a   an argument.
     * @param   b   another argument.
     * @return  the smaller of <code>a</code> and <code>b</code>.
     */
    /*@
      @ public normal_behavior
      @  ensures \result == ((a <= b) ? a : b);
      @
      @ model public static pure \real min(\real a, \real b) {
      @   return (a <= b) ? a : b;
      @ }
      @*/

}
