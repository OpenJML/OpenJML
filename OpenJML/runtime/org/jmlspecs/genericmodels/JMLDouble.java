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

package org.jmlspecs.genericmodels;
import org.jmlspecs.annotation.*;

/** A reflection of {@link java.lang.Double} that implements {@link JMLType}.
 *
 * @version $Revision: 1.34 $
 * @author Brandon Shilling
 * @author Gary T. Leavens
 * @author David Cok
 * @see java.lang.Double
 * @see JMLDouble
 */
//+OPENJML@ immutable
public @Pure strictfp class JMLDouble implements JMLComparable<JMLDouble> {

    private static final long serialVersionUID = 1L;
    
    /** The double that is the abstract value of this object.
     */
    //@ model public double theDouble;

    /*@ spec_public @*/ private double doubleValue;
    //@                                   in theDouble;
    //@ private represents theDouble <- doubleValue;

    //@ public invariant owner == null;

    /** Initialize this object to contain zero.
     */
    /*@ public normal_behavior
      @   assignable theDouble,owner;
      @   ensures theDouble == 0.0d;
      @*/
    public JMLDouble ( ) {
        doubleValue = 0.0d;
        //@ set owner = null;
    } 
   
    /** Initialize this object to contain the given double.
     */
    /*@   public normal_behavior
      @     requires !Double.isNaN(inDouble);
      @     assignable theDouble,owner;
      @     ensures theDouble == inDouble;
      @ also
      @   public normal_behavior
      @     requires Double.isNaN(inDouble);
      @     assignable theDouble,owner;
      @     ensures Double.isNaN(theDouble);
      @*/ 
    public JMLDouble (double inDouble) {
        doubleValue = inDouble;
        //@ set owner = null;
    } 

    /** Initialize this object to contain an approximation to the
     * given integer.
     */
    /*@ public normal_behavior
      @   assignable theDouble,owner;
      @   ensures theDouble == (double)inInt;
      @*/
    public JMLDouble (int inInt) {
        doubleValue = (double)inInt;
        //@ set owner = null;
    } 

    /** Initialize this object to contain the value of the given
     * Double.
     */
    /*@   public normal_behavior
      @     requires inDouble != null && !inDouble.isNaN();
      @     assignable theDouble,owner;
      @     ensures theDouble == inDouble.doubleValue();
      @ also
      @   public normal_behavior
      @     requires inDouble != null && inDouble.isNaN();
      @     assignable theDouble,owner;
      @     ensures Double.isNaN(theDouble);
      @*/
    public JMLDouble(/*@ non_null */ Double inDouble) {
        doubleValue = inDouble.doubleValue();
        //@ set owner = null;
    }

    /** Initialize this object to contain the value given by the
     * string argument.
     */
    /*@ public behavior
      @     requires s != null;
      @     assignable theDouble,owner;
      @     ensures (* s is a parseable string that has the format
      @                of a double precision floating point literal *)
      @         && theDouble == new Double(s).doubleValue();
      @     signals_only NumberFormatException;
      @     signals (NumberFormatException)
      @             !(* s is a parseable string that has the format
      @                of a double precision floating point literal *);
      @*/
    public JMLDouble (/*@ non_null @*/ String s) throws NumberFormatException {
        doubleValue = Double.parseDouble(s);
        //@ set owner = null;
    }

    /** Tell if this object contains either positive or negative infinity.
     */
    /*@ public normal_behavior
      @   ensures \result <==> (theDouble == Double.POSITIVE_INFINITY) 
      @                   || (theDouble == Double.NEGATIVE_INFINITY);
      @*/
    public boolean isInfinite() {
  	return (doubleValue == Double.POSITIVE_INFINITY)
            || (doubleValue == Double.NEGATIVE_INFINITY);
    }

    /** Tell if this object contains NaN (not a number).
     */
    /*@ public normal_behavior
      @   ensures \result <==> (theDouble != theDouble); 
      @*/
    public boolean isNaN() {
	return (doubleValue != doubleValue);
    }

    /** Return a clone of this object.
     */
    /*@ also
      @   public normal_behavior
      @     requires !Double.isNaN(theDouble);
      @     ensures \result != null && \result instanceof JMLDouble 
      @             && ((JMLDouble)\result).theDouble == theDouble; 
      @ also
      @   public normal_behavior
      @     requires Double.isNaN(theDouble);
      @     ensures \result != null && \result instanceof JMLDouble 
      @             && ((JMLDouble)\result).isNaN();
      @*/
    public Object clone() {
        return this;
    }
   
    /** Compare this to op2, returning a comparison code.
     *  @param op2 the object this is compared to.
     */
    // FIXME - explain why we use Double.compareTo instead of comparing doubles
    public int compareTo(@NonNull JMLDouble op2) {
        return new Double(doubleValue)
            .compareTo(new Double(op2.doubleValue));
    }

    /** Tell if the argument is zero (either positive or negative).
     */
    /*@ public normal_behavior
      @   ensures \result <==> (d == +0.0d || d == -0.0d);
      @*/
    public static @Pure boolean isZero(double d) {
        return d == +0.0d || d == -0.0d;
    }
  
    /** Tell if this object contains zero (either positive or negative).
     */
    /*@ public normal_behavior
      @   ensures \result <==> (theDouble == +0.0d || theDouble == -0.0d);
      @*/
    public boolean isZero() {
        return doubleValue == +0.0d || doubleValue == -0.0d;
    }

    /** Tell whether this object is equal to the argument.
     */
    /*@ also
      @   public normal_behavior
      @     requires (op2 instanceof JMLDouble) && op2 != null;
      @     {|
      @       requires !Double.isNaN(theDouble) && !isZero();
      @       ensures \result <==> theDouble == ((JMLDouble)op2).theDouble; 
      @     also
      @       requires Double.isNaN(theDouble);
      @       ensures \result <==> Double.isNaN(((JMLDouble)op2).theDouble); 
      @     also
      @       requires isZero();
      @       ensures \result <==> ((JMLDouble)op2).isZero();
      @     |}
      @ also
      @   public normal_behavior
      @     requires !(op2 instanceof JMLDouble) || op2 == null;
      @     ensures \result <==> false;
      @*/
    public boolean equals(@Nullable Object op2) {
        if (op2 == null || !(op2 instanceof JMLDouble)) {
            return false;
        }
        JMLDouble jmld2 = (JMLDouble)op2;
        double dv2 = jmld2.doubleValue;
        if (Double.isNaN(doubleValue) && Double.isNaN(dv2)) {
            return true;
        } else if (isZero() && jmld2.isZero()) {
            return true;
        } else {
            return doubleValue == dv2;
        }
    } 

    /** Return a hash code for this object.
     */
    public int hashCode() {
        return Double.valueOf(doubleValue).hashCode();
    }

    /** Return the double contained in this object.
     */
    /*@ public normal_behavior
      @   requires !isNaN();
      @   ensures \result == doubleValue;
      @ also
      @   requires isNaN();
      @   ensures Double.isNaN(\result);
      @*/
    public double doubleValue() {
        return doubleValue;
    }

    /** Return a Double containing the double contained in this object.
     */
    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures !isNaN() ==> theDouble == \result.doubleValue();
      @   ensures isNaN() ==> \result.isNaN();
      @*/
    public @NonNull Double getDouble() {
        return Double.valueOf(doubleValue);
    }

    /** Return the negation of this.
     */
    /*@ public normal_behavior
      @    ensures \result != null;
      @    ensures \result.equals(new JMLDouble(\nowarn(- theDouble)));
      @*/
    public @NonNull JMLDouble negated() {
        return new JMLDouble(- doubleValue);
    }

    /** Return the sum of this and the given argument.
     */
    /*@ public normal_behavior
      @    requires d2 != null;
      @    ensures \result != null;
      @    ensures \result.equals(new JMLDouble(\nowarn(theDouble + d2.theDouble)));
      @*/
    public @NonNull JMLDouble plus(@NonNull JMLDouble d2) {
        return new JMLDouble(doubleValue + d2.doubleValue());
    }

    /** Return the difference between this and the given argument.
     */
    /*@ public normal_behavior
      @    requires d2 != null;
      @    ensures \result != null;
      @    ensures \result.equals(new JMLDouble(\nowarn(theDouble - d2.theDouble)));
      @*/
    public @NonNull JMLDouble minus(@NonNull JMLDouble d2) {
        return new JMLDouble(doubleValue - d2.doubleValue());
    }

    /** Return the product of this and the given argument.
     */
    /*@   public normal_behavior
      @      requires d2 != null;
      @      ensures \result != null
      @             && \result.equals(new JMLDouble(\nowarn(theDouble * d2.theDouble)));
      @ implies_that
      @   public normal_behavior
      @      requires d2 != null;
      @      requires d2.isNaN()
      @            || (this.isZero() && d2.isInfinite())
      @            || (d2.isZero() && this.isInfinite());
      @         ensures \result != null && \result.isNaN();
      @*/
    public @NonNull JMLDouble times(@NonNull JMLDouble d2) {
        return new JMLDouble(doubleValue * d2.doubleValue());
    }

    /** Return the quotient of this divided by the given argument.
     */
    /*@   public normal_behavior
      @      requires d2 != null;
      @      ensures \result != null
      @           && \result.equals(new JMLDouble(\nowarn(theDouble / d2.theDouble)));
      @ implies_that
      @   public normal_behavior
      @      requires d2 != null;
      @         requires d2.isZero() || d2.isNaN();
      @         ensures \result != null && \result.isNaN();
      @*/
    public @NonNull
        JMLDouble dividedBy(@NonNull JMLDouble d2) {
        return new JMLDouble(doubleValue / d2.doubleValue());
    }

    /** Return the remainder of this divided by the given argument.
     */
    /*@   public normal_behavior
      @      requires d2 != null;
      @      ensures \result != null
      @           && \result.equals(new JMLDouble(theDouble % d2.theDouble));
      @ implies_that
      @   public normal_behavior
      @      requires d2 != null;
      @         requires d2.isZero() || d2.isNaN();
      @         ensures \result != null && \result.isNaN();
      @*/
    public @NonNull
        JMLDouble remainderBy(@NonNull JMLDouble d2) {
        return new JMLDouble(doubleValue % d2.doubleValue());
    }

    /** Tell whether this is strictly greater than the given argument.
     */
    /*@ public normal_behavior
      @   requires d2 != null;
      @   ensures \result <==> this.theDouble > d2.theDouble;
      @*/
    public boolean greaterThan(@NonNull JMLDouble d2) {
        return (doubleValue > d2.doubleValue());
    }

    /** Tell whether this is strictly less than the given argument.
     */
    /*@ public normal_behavior
      @   requires d2 != null;
      @   ensures \result <==> this.theDouble < d2.theDouble;
      @*/
    public boolean lessThan(@NonNull JMLDouble d2) {
        return (doubleValue < d2.doubleValue());
    }

    /** Tell whether this is greater than or equal to the given argument.
     */
    /*@ public normal_behavior
      @   requires d2 != null;
      @   ensures \result <==> this.theDouble >= d2.theDouble;
      @*/
    public boolean greaterThanOrEqualTo(@NonNull JMLDouble d2) {
        return (doubleValue >= d2.doubleValue());
    }

    /** Tell whether this is less than or equal to the given argument.
     */
    /*@ public normal_behavior
      @   requires d2 != null;
      @   ensures \result <==> this.theDouble <= d2.theDouble;
      @*/
    public boolean lessThanOrEqualTo(@NonNull JMLDouble d2) {
        return (doubleValue <= d2.doubleValue());
    }
   
    /** Return a string representation of this object.
     */
    // specification inherited from Object
    public @NonNull String toString() {
        return String.valueOf(doubleValue);
    }

    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires d2 != null;
      @    ensures \result <==> 
      @             StrictMath.abs(\nowarn(theDouble - d2.theDouble)) <= epsilon;
      @*/
    public boolean withinEpsilonOf(@NonNull JMLDouble d2,
                                   double epsilon) {
        return StrictMath.abs(doubleValue()-d2.doubleValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires d2 != null;
      @    ensures \result
      @       <==> approximatelyEqualTo(theDouble, d2.theDouble, epsilon);
      @*/
    public boolean approximatelyEqualTo(@NonNull JMLDouble d2,
                                        double epsilon) {
        return approximatelyEqualTo(doubleValue(), d2.doubleValue(), epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires d2 != null;
      @    ensures \result <==> 
      @             StrictMath.abs(\nowarn(theDouble - d2.doubleValue())) <= epsilon;
      @*/
    public boolean withinEpsilonOf(@NonNull Double d2,
                                   double epsilon) {
        return StrictMath.abs(doubleValue()-d2.doubleValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires d2 != null;
      @    ensures \result
      @       <==> approximatelyEqualTo(theDouble, d2.doubleValue(), epsilon);
      @*/
    public boolean approximatelyEqualTo(@NonNull Double d2,
                                        double epsilon) {
        return approximatelyEqualTo(doubleValue(), d2.doubleValue(), epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    ensures \result <==>
      @         StrictMath.abs(\nowarn(theDouble - d2)) <= epsilon;
      @*/
    public boolean withinEpsilonOf(double d2, double epsilon) {
        return StrictMath.abs(doubleValue()-d2) <= epsilon;
    }

    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    ensures \result
      @       <==> approximatelyEqualTo(theDouble, d2, epsilon);
      @*/
    public boolean approximatelyEqualTo(double d2, double epsilon) {
        return approximatelyEqualTo(doubleValue(), d2, epsilon);
    }    
    
    /** Tell whether absolute value of difference of the two arguments
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    ensures \result <==>
      @         StrictMath.abs(\nowarn(d1 - d2)) <= epsilon;
      @*/
    public static @Pure boolean withinEpsilonOf(double d1, double d2,
                                                         double epsilon)
    {
        return StrictMath.abs(d1-d2) <= epsilon;
    }

    /** Tell whether relative difference of the two arguments is 
     *   within the given epsilon.
     */
    /*@ public normal_behavior
      @    ensures \result <==>
      @      d1 == d2
      @      || StrictMath.abs(\nowarn(d1 - d2))
      @            <= StrictMath.max(StrictMath.abs(d1),
      @                              StrictMath.abs(d2))
      @               * epsilon;
      @*/
    public static @Pure boolean approximatelyEqualTo(
        double d1, double d2, double epsilon)
    {
        return d1 == d2
            || StrictMath.abs(d1-d2)
               <= StrictMath.max(StrictMath.abs(d1),
                                 StrictMath.abs(d2))
                  * epsilon;
    }    

    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires d1 != null && d2 != null;
      @    ensures \result <==> 
      @             StrictMath.abs(\nowarn(d1.theDouble - d2.theDouble)) <= epsilon;
      @*/
    public static @Pure boolean withinEpsilonOf(
                                          @NonNull JMLDouble d1,
                                          @NonNull JMLDouble d2,
                                          double epsilon) {
        return StrictMath.abs(d1.doubleValue()-d2.doubleValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires d1 != null && d2 != null;
      @    ensures \result
      @       <==> approximatelyEqualTo(d1.theDouble, d2.theDouble, epsilon);
      @*/
    public static @Pure boolean approximatelyEqualTo(
                                               @NonNull JMLDouble d1,
                                               @NonNull JMLDouble d2,
                                               double epsilon) {
        return approximatelyEqualTo(d1.doubleValue(), d2.doubleValue(),
                                    epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires d1 != null && d2 != null;
      @    ensures \result <==>
      @         StrictMath.abs(\nowarn(d1.theDouble - d2.doubleValue())) <= epsilon;
      @*/
    public static @Pure boolean withinEpsilonOf(
                                          @NonNull JMLDouble d1,
                                          @NonNull Double d2,
                                          double epsilon) {
        return StrictMath.abs(d1.doubleValue()-d2.doubleValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires d1 != null && d2 != null;
      @    ensures \result
      @     <==> approximatelyEqualTo(d1.theDouble, d2.doubleValue(), epsilon);
      @*/
    public static @Pure boolean approximatelyEqualTo(
                                               @NonNull JMLDouble d1,
                                               @NonNull Double d2,
                                               double epsilon) {
        return approximatelyEqualTo(d1.doubleValue(), d2.doubleValue(),
                                    epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires d1 != null;
      @    ensures \result <==> StrictMath.abs(\nowarn(d1.theDouble - d2)) <= epsilon;
      @*/
    public static @Pure boolean withinEpsilonOf(
                                          @NonNull JMLDouble d1,
                                          double d2,
                                          double epsilon) {
        return StrictMath.abs(d1.doubleValue()-d2) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires d1 != null;
      @    ensures \result
      @       <==> approximatelyEqualTo(d1.theDouble, d2, epsilon);
      @*/
    public static @Pure boolean approximatelyEqualTo(
                                               @NonNull JMLDouble d1,
                                               double d2,
                                               double epsilon) {
        return approximatelyEqualTo(d1.doubleValue(), d2, epsilon);
    }
}
