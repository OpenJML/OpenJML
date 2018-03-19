// @(#)$Id: JMLFloat.java,v 1.36 2007/02/08 14:05:50 leavens Exp $

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

/** A reflection of {@link java.lang.Float} that implements {@link JMLType}.
 *
 * @version $Revision: 1.36 $
 * @author Brandon Shilling
 * @author Gary T. Leavens
 * @author David Cok
 * @see java.lang.Float
 * @see JMLDouble
 */
//+OPENJML@ immutable
public /*@ pure @*/ strictfp class JMLFloat implements JMLComparable {

    /** The float that is the abstract value of this object.
     */
    //@ model public float theFloat;

    /*@ spec_public @*/ private float floatValue;
    //@                                   in theFloat;
    //@ private represents theFloat <- floatValue;

    //@ public invariant owner == null;

    /** Initialize this object to contain zero.
     */
    /*@ public normal_behavior
      @   assignable theFloat,owner;
      @   ensures theFloat == 0.0f;
      @*/
    public JMLFloat ( ) {
        floatValue = 0.0f;
        //@ set owner = null;
    } 
   
    /** Initialize this object to contain the given float.
     */
    /*@   public normal_behavior
      @     requires !Float.isNaN(inFloat);
      @     assignable theFloat,owner;
      @     ensures theFloat == inFloat;
      @ also
      @   public normal_behavior
      @     requires Float.isNaN(inFloat);
      @     assignable theFloat,owner;
      @     ensures Float.isNaN(theFloat);
      @*/ 
    public JMLFloat (float inFloat) {
        floatValue = inFloat;
        //@ set owner = null;
    } 

    /** Initialize this object to contain an approximation to the
     * given integer.
     */
    /*@ public normal_behavior
      @   assignable theFloat,owner;
      @   ensures theFloat == (float)inInt;
      @*/
    public JMLFloat (int inInt) {
        floatValue = (float)inInt;
        //@ set owner = null;
    } 

    /** Initialize this object to contain the value of the given
     * Float.
     */
    /*@   public normal_behavior
      @     requires inFloat != null && !inFloat.isNaN();
      @     assignable theFloat,owner;
      @     ensures theFloat == inFloat.floatValue();
      @ also
      @   public normal_behavior
      @     requires inFloat != null && inFloat.isNaN();
      @     assignable theFloat,owner;
      @     ensures Float.isNaN(theFloat);
      @*/
    public JMLFloat(/*@ non_null */ Float inFloat) {
        floatValue = inFloat.floatValue();
        //@ set owner = null;
    }

    /** Initialize this object to contain the value given by the
     * string argument.
     */
    /*@ public behavior
      @     requires s != null;
      @     assignable theFloat,owner;
      @     ensures (* s is a parseable string that has the format
      @                of a floating point literal *)
      @         && theFloat == Float.valueOf(s).floatValue();
      @     signals_only NumberFormatException;
      @     signals (NumberFormatException)
      @             !(* s is a parseable string that has the format
      @                 of a floating point literal *);
      @*/
    public JMLFloat (/*@ non_null @*/ String s) throws NumberFormatException {
        floatValue = Float.valueOf(s).floatValue();
        //@ set owner = null;
    }

    /** Tell if this object contains either positive or negative infinity.
     */
    /*@ public normal_behavior
      @   ensures \result <==> (theFloat == Float.POSITIVE_INFINITY) 
      @                   || (theFloat == Float.NEGATIVE_INFINITY);
      @*/
    public boolean isInfinite() {
  	return (floatValue == Float.POSITIVE_INFINITY)
            || (floatValue == Float.NEGATIVE_INFINITY);
    }

    /** Tell if this object contains NaN (not a number).
     */
    /*@ public normal_behavior
      @   ensures \result <==> (theFloat != theFloat); 
      @*/
    public boolean isNaN() {
	return (floatValue != floatValue);
    }

    /** Return a clone of this object.
     */
    /*@ also
      @   public normal_behavior
      @     requires !Float.isNaN(theFloat);
      @     ensures \result != null && \result instanceof JMLFloat 
      @             && ((JMLFloat)\result).theFloat == theFloat; 
      @ also
      @   public normal_behavior
      @     requires Float.isNaN(theFloat);
      @     ensures \result != null && \result instanceof JMLFloat 
      @             && ((JMLFloat)\result).isNaN();
      @*/
    public Object clone() {
        return this;
    }
   
    /** Compare this to op2, returning a comparison code.
     *  @param op2 the object this is compared to.
     *  @exception ClassCastException when o is not a JMLFloat.
     */
    public int compareTo(/*@ non_null @*/ Object op2) throws ClassCastException {
        return Float.valueOf(floatValue)
            .compareTo(Float.valueOf(((JMLFloat)op2)  //@ nowarn Cast;
                                  .floatValue));
    }

    /** Tell if the argument is zero (either positive or negative).
     */
    /*@ public normal_behavior
      @   ensures \result <==> (f == +0.0f || f == -0.0f);
      @*/
    public static /*@ pure @*/ boolean isZero(float f) {
        return f == +0.0f || f == -0.0f;
    }

    /** Tell if this object contains zero (either positive or negative).
     */
    /*@ public normal_behavior
      @   ensures \result <==> (theFloat == +0.0f || theFloat == -0.0f);
      @*/
    public boolean isZero() {
        return floatValue == +0.0f || floatValue == -0.0f;
    }
  
    /** Tell whether this object is equal to the argument.
     */
    /*@ also
      @   public normal_behavior
      @     requires (op2 instanceof JMLFloat) && op2 != null;
      @     {|
      @       requires !Float.isNaN(theFloat) && !isZero();
      @       ensures \result <==> theFloat == ((JMLFloat)op2).theFloat; 
      @     also
      @       requires Float.isNaN(theFloat);
      @       ensures \result <==> Float.isNaN(((JMLFloat)op2).theFloat); 
      @     also
      @       requires isZero();
      @       ensures \result <==> ((JMLFloat)op2).isZero();
      @     |}
      @ also
      @   public normal_behavior
      @     requires !(op2 instanceof JMLFloat) || op2 == null;
      @     ensures \result <==> false;
      @*/
    public boolean equals(/*@ nullable @*/ Object op2) {
        if (op2 == null || !(op2 instanceof JMLFloat)) {
            return false;
        }
        JMLFloat jmlf2 = (JMLFloat)op2;
        float fv2 = jmlf2.floatValue;
        if (Float.isNaN(floatValue) && Float.isNaN(fv2)) {
            return true;
        } else if (isZero() && jmlf2.isZero()) {
            return true;
        } else {
            return floatValue == fv2;
        }
    } 

    /** Return a hash code for this object.
     */
    public int hashCode() {
        return Float.valueOf(floatValue).hashCode();
    }

    /** Return the float contained in this object.
     */
    /*@ public normal_behavior
      @   requires !isNaN();
      @   ensures \result == floatValue;
      @ also
      @   requires isNaN();
      @   ensures Float.isNaN(\result);
      @*/
    public float floatValue() {
        return floatValue;
    }

    /** Return a Float containing the float contained in this object.
     */
    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures !isNaN() ==> theFloat == \result.floatValue();
      @   ensures isNaN() ==> \result.isNaN();
      @*/
    public /*@ non_null @*/ Float getFloat() {
        return Float.valueOf(floatValue);
    }

    /** Return the negation of this.
     */
    /*@ public normal_behavior
      @    ensures \result != null;
      @    ensures \result.equals(new JMLFloat(\nowarn(- theFloat)));
      @*/
    public /*@ non_null @*/ JMLFloat negated() {
        return new JMLFloat(- floatValue);
    }

    /** Return the sum of this and the given argument.
     */
    /*@ public normal_behavior
      @    requires f2 != null;
      @    ensures \result != null;
      @    ensures \result.equals(new JMLFloat(\nowarn(theFloat + f2.theFloat)));
      @*/
    public /*@ non_null @*/ JMLFloat plus(/*@ non_null */ JMLFloat f2) {
        return new JMLFloat(floatValue + f2.floatValue());
    }

    /** Return the difference between this and the given argument.
     */
    /*@ public normal_behavior
      @    requires f2 != null;
      @    ensures \result != null;
      @    ensures \result.equals(new JMLFloat(\nowarn(theFloat - f2.theFloat)));
      @*/
    public /*@ non_null @*/ JMLFloat minus(/*@ non_null */ JMLFloat f2) {
        return new JMLFloat(floatValue - f2.floatValue());
    }

    /** Return the product of this and the given argument.
     */
    /*@   public normal_behavior
      @      requires f2 != null;
      @      ensures \result != null
      @             && \result.equals(new JMLFloat(\nowarn(theFloat * f2.theFloat)));
      @ implies_that
      @   public normal_behavior
      @      requires f2 != null;
      @      requires f2.isNaN()
      @            || (this.isZero() && f2.isInfinite())
      @            || (f2.isZero() && this.isInfinite());
      @         ensures \result != null && \result.isNaN();
      @*/
    public /*@ non_null @*/ JMLFloat times(/*@ non_null */ JMLFloat f2) {
        return new JMLFloat(floatValue * f2.floatValue());
    }

    /** Return the quotient of this divided by the given argument.
     */
    /*@   public normal_behavior
      @      requires f2 != null;
      @      ensures \result != null
      @           && \result.equals(new JMLFloat(\nowarn(theFloat / f2.theFloat)));
      @ implies_that
      @   public normal_behavior
      @      requires f2 != null;
      @         requires f2.isZero() || f2.isNaN();
      @         ensures \result != null && \result.isNaN();
      @*/
    public /*@ non_null @*/
        JMLFloat dividedBy(/*@ non_null */ JMLFloat f2) {
        return new JMLFloat(floatValue / f2.floatValue());
    }

    /** Return the remainder of this divided by the given argument.
     */
    /*@   public normal_behavior
      @      requires f2 != null;
      @      ensures \result != null
      @           && \result.equals(new JMLFloat(theFloat % f2.theFloat));
      @ implies_that
      @   public normal_behavior
      @      requires f2 != null;
      @         requires f2.isZero() || f2.isNaN();
      @         ensures \result != null && \result.isNaN();
      @*/
    public /*@ non_null @*/
        JMLFloat remainderBy(/*@ non_null @*/ JMLFloat f2) {
        return new JMLFloat(floatValue % f2.floatValue());
    }

    /** Tell whether this is strictly greater than the given argument.
     */
    /*@ public normal_behavior
      @   requires f2 != null;
      @   ensures \result <==> this.theFloat > f2.theFloat;
      @*/
    public boolean greaterThan(/*@ non_null */ JMLFloat f2) {
        return (floatValue > f2.floatValue());
    }

    /** Tell whether this is strictly less than the given argument.
     */
    /*@ public normal_behavior
      @   requires f2 != null;
      @   ensures \result <==> this.theFloat < f2.theFloat;
      @*/
    public boolean lessThan(/*@ non_null */ JMLFloat f2) {
        return (floatValue < f2.floatValue());
    }

    /** Tell whether this is greater than or equal to the given argument.
     */
    /*@ public normal_behavior
      @   requires f2 != null;
      @   ensures \result <==> this.theFloat >= f2.theFloat;
      @*/
    public boolean greaterThanOrEqualTo(/*@ non_null */ JMLFloat f2) {
        return (floatValue >= f2.floatValue());
    }

    /** Tell whether this is less than or equal to the given argument.
     */
    /*@ public normal_behavior
      @   requires f2 != null;
      @   ensures \result <==> this.theFloat <= f2.theFloat;
      @*/
    public boolean lessThanOrEqualTo(/*@ non_null */ JMLFloat f2) {
        return (floatValue <= f2.floatValue());
    }
   
    /** Return a string representation of this object.
     */
    // specification inherited from Object
    public String toString() {
        return String.valueOf(floatValue);
    }

    /** Tell whether absolute value of difference of this JMLFloat and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires f2 != null;
      @    assignable \nothing;
      @    ensures \result <==> 
      @             StrictMath.abs(\nowarn(theFloat - f2.theFloat)) <= epsilon;
      @*/
    public boolean withinEpsilonOf(/*@ non_null @*/ JMLFloat f2,
                                   float epsilon) {
        return StrictMath.abs(floatValue()-f2.floatValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLFloat and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(float, float, float)
     */
    /*@ public normal_behavior
      @    requires f2 != null;
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(theFloat, f2.theFloat, epsilon);
      @*/
    public boolean approximatelyEqualTo(/*@ non_null @*/ JMLFloat f2,
                                        float epsilon) {
        return approximatelyEqualTo(floatValue(), f2.floatValue(), epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLFloat and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires f2 != null;
      @    assignable \nothing;
      @    ensures \result <==> 
      @             StrictMath.abs(\nowarn(theFloat - f2.floatValue())) <= epsilon;
      @*/
    public boolean withinEpsilonOf(/*@ non_null @*/ Float f2,
                                   float epsilon) {
        return StrictMath.abs(floatValue()-f2.floatValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLFloat and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(float, float, float)
     */
    /*@ public normal_behavior
      @    requires f2 != null;
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(theFloat, f2.floatValue(), epsilon);
      @*/
    public boolean approximatelyEqualTo(/*@ non_null @*/ Float f2,
                                        float epsilon) {
        return approximatelyEqualTo(floatValue(), f2.floatValue(), epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLFloat and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures \result <==>
      @         StrictMath.abs(\nowarn(theFloat - f2)) <= epsilon;
      @*/
    public boolean withinEpsilonOf(float f2, float epsilon) {
        return StrictMath.abs(floatValue()-f2) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLFloat and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(float, float, float)
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(theFloat, f2, epsilon);
      @*/
    public boolean approximatelyEqualTo(float f2, float epsilon) {
        return approximatelyEqualTo(floatValue(), f2, epsilon);
    }
        
    /** Tell whether absolute value of difference of the two arguments
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures \result <==>
      @         StrictMath.abs(\nowarn(f1 - f2)) <= epsilon;
      @*/
    public static /*@ pure @*/ boolean withinEpsilonOf(float f1, float f2,
                                                         float epsilon)
    {
        return StrictMath.abs(f1-f2) <= epsilon;
    }
    
    /** Tell whether relative difference of the two arguments is 
     *   within the given epsilon.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures \result <==>
      @      f1 == f2
      @      || StrictMath.abs(\nowarn(f1 - f2))
      @            <= StrictMath.max(StrictMath.abs(f1),
      @                              StrictMath.abs(f2))
      @               * epsilon;
      @*/
    public static /*@ pure @*/ boolean approximatelyEqualTo(
        float f1, float f2, float epsilon)
    {
        return f1 == f2
            || StrictMath.abs(f1-f2)
               <= StrictMath.max(StrictMath.abs(f1),
                                 StrictMath.abs(f2))
                  * epsilon;
    }

    /** Tell whether absolute value of difference of this JMLFloat and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires f1 != null && f2 != null;
      @    assignable \nothing;
      @    ensures \result <==>
      @         StrictMath.abs(\nowarn(f1.theFloat - f2.theFloat)) <= epsilon;
      @*/
    public static /*@ pure @*/ boolean withinEpsilonOf(
                                          /*@ non_null @*/ JMLFloat f1,
                                          /*@ non_null @*/ JMLFloat f2,
                                          float epsilon) {
        return StrictMath.abs(f1.floatValue()-f2.floatValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLFloat and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(float, float, float)
     */
    /*@ public normal_behavior
      @    requires f1 != null && f2 != null;
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(f1.theFloat, f2.theFloat, epsilon);
      @*/
    public static /*@ pure @*/ boolean approximatelyEqualTo(
                                               /*@ non_null @*/ JMLFloat f1,
                                               /*@ non_null @*/ JMLFloat f2,
                                               float epsilon) {
        return approximatelyEqualTo(f1.floatValue(), f2.floatValue(), epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLFloat and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires f1 != null && f2 != null;
      @    assignable \nothing;
      @    ensures \result <==>
      @         StrictMath.abs(\nowarn(f1.theFloat - f2.floatValue())) <= epsilon;
      @*/
    public static /*@ pure @*/ boolean withinEpsilonOf(
                                          /*@ non_null @*/ JMLFloat f1,
                                          /*@ non_null @*/ Float f2,
                                          float epsilon) {
        return StrictMath.abs(f1.floatValue()-f2.floatValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLFloat and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(float, float, float)
     */
    /*@ public normal_behavior
      @    requires f1 != null && f2 != null;
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(f1.theFloat, f2.floatValue(), epsilon);
      @*/
    public static /*@ pure @*/ boolean approximatelyEqualTo(
                                               /*@ non_null @*/ JMLFloat f1,
                                               /*@ non_null @*/ Float f2,
                                               float epsilon) {
        return approximatelyEqualTo(f1.floatValue(), f2.floatValue(), epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLFloat and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires f1 != null;
      @    assignable \nothing;
      @    ensures \result <==> StrictMath.abs(\nowarn(f1.theFloat - f2)) <= epsilon;
      @*/
    public static /*@ pure @*/ boolean withinEpsilonOf(
                                          /*@ non_null @*/ JMLFloat f1,
                                          float f2,
                                          float epsilon) {
        return StrictMath.abs(f1.floatValue()-f2) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLFloat and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(float, float, float)
     */
    /*@ public normal_behavior
      @    requires f1 != null;
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(f1.theFloat, f2, epsilon);
      @*/
    public static /*@ pure @*/ boolean approximatelyEqualTo(
                                               /*@ non_null @*/ JMLFloat f1,
                                               float f2,
                                               float epsilon) {
        return approximatelyEqualTo(f1.floatValue(), f2, epsilon);
    }
}
