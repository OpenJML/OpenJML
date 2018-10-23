// @(#)$Id: JMLShort.java,v 1.27 2007/02/08 14:05:50 leavens Exp $

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

/** A reflection of {@link java.lang.Short} that implements {@link JMLType}.
 *
 * @version $Revision: 1.27 $
 * @author Gary T. Leavens
 * @author Brandon Shilling
 * @see java.lang.Short
 * @see JMLChar
 * @see JMLByte
 * @see JMLInteger
 * @see JMLLong
 * @see JMLType
 */
//+OPENJML@ immutable
public /*@ pure @*/ class JMLShort implements JMLComparable {

    /*@ axiom (\forall Comparable s; (\forall JMLShort ss,sss; 
		(ss instanceof JMLShort && sss instanceof JMLShort) ==>
			s.definedComparison(ss,sss) )); */

    /** The short value of this object.
     */
    //@ public model short theShort;

    //@ public constraint theShort == \old(theShort);

    private short shortValue;
    //@              in theShort;
    //@ private represents theShort <- shortValue;

    //@ public  invariant owner == null;

    /** Initialize this object to 0.
     */
    /*@  public normal_behavior
      @    assignable theShort, owner;
      @    ensures theShort == 0;
      @*/
    public JMLShort ( ) {
        shortValue = 0;
        //@ set owner = null;
    } 

    /** Initialize this object to the given short.
     */
    /*@  public normal_behavior
      @    assignable theShort, owner;
      @    ensures theShort == inShort;
      @*/
    public JMLShort (short inShort) {
        shortValue = inShort;
        //@ set owner = null;
    } 

    /** Initialize this object to the given short.
     *  @param inShort an object containing the value to use.
     */
    /*@  public normal_behavior
      @    requires inShort != null;
      @    assignable theShort, owner;
      @    ensures theShort == inShort.shortValue();
      @*/
    public JMLShort(/*@ non_null */ Short inShort) {
        shortValue = inShort.shortValue();
        //@ set owner = null;
    }

    /** Initialize this object to the given short.
     *  @param s a string that contains the decimal representation of
     *  the desired value.
     */
    /*@  public behavior
      @    requires s != null
      @          && (* s is a properly formatted short literal *);
      @    assignable theShort, owner;
      @    ensures theShort == (new Short(s)).shortValue();
      @*/
    public JMLShort (/*@ non_null @*/ String s) throws JMLTypeException {
        //@ set owner = null;
        try {
            shortValue = Short.valueOf(s).shortValue(); //@ nowarn Null;
        } catch (RuntimeException re) {
            throw new JMLTypeException("Bad format string passed to "
                                       + "JMLShort(String): \""
                                       + s + "\"");
        }
    }

    /** The JMLShort that represents zero.
     */
    public static final JMLShort ZERO = new JMLShort();
   
    /** The JMLShort that represents one.
     */
    public static final JMLShort ONE = new JMLShort((short)1);

    /** Return a clone of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof JMLShort
      @     	  && ((JMLShort)\result).theShort == theShort;
      @*/
    public Object clone() {
        return this;
    }
   
    /** Compare this to op2, returning a comparison code.
     *  @param op2 the object this is compared to.
     *  @exception ClassCastException when o is not a JMLShort.
     */
    /*@ also
      @   public normal_behavior
      @    requires op2 instanceof JMLShort;
      @    ensures (theShort < ((JMLShort)op2).theShort ==> \result == -1)
      @         && (theShort == ((JMLShort)op2).theShort ==> \result == 0)
      @         && (theShort > ((JMLShort)op2).theShort ==> \result == +1);
      @ also
      @   public exceptional_behavior
      @    requires op2 != null && !(op2 instanceof JMLShort);
      @    signals_only ClassCastException;
      @*/
    public int compareTo(/*@ non_null @*/ Object op2) throws ClassCastException {
        if (op2 instanceof JMLShort) {
            short sv2 = ((JMLShort)op2).shortValue;
            if (shortValue < sv2) {
                return -1;
            } else if (shortValue == sv2) {
                return 0;
            } else {
                return +1;
            }
        } else {
            throw new ClassCastException();
        }
    }

    /** Test whether this object's value is equal to the given argument.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result <==> op2 != null && op2 instanceof JMLShort 
      @                          && theShort == ((JMLShort)op2).theShort;
      @*/
    //+OPENJML@ function
    public boolean equals(/*@ nullable @*/ Object op2) {
        return op2 != null && op2 instanceof JMLShort
            && shortValue == ((JMLShort)op2).shortValue;
    } 

    /** Return a hash code for this object.
     */
    public /*@ pure @*/ int hashCode() {
        return shortValue;
    }

    /** Return the short value in this object.
     */
    /*@  public normal_behavior
      @    ensures \result == theShort;
      @*/
    public short shortValue() {
        return shortValue;
    }

    /** Return an Short object containing the short value in this
     * object.
     */
    /*@  public normal_behavior
      @    ensures \result != null && \result.equals(new Short(theShort));
      @*/
    public /*@ non_null @*/ Short getShort() {
        return Short.valueOf(shortValue);
    }

    /** Return a new object containing the negation of this object's
     * short value.
     */
    /*@  public normal_behavior
      @    ensures \result != null && 
      @      \result.theShort == \nowarn_op((short)- theShort);
      @*/
    public /*@ non_null @*/ JMLShort negated() {
        return new JMLShort((short)- shortValue);
    }

    /** Return a new object containing the sum of this object's
     *  short value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theShort == \nowarn_op((short)(theShort + i2.theShort));
      @*/
    public /*@ non_null @*/ JMLShort plus(/*@ non_null @*/ JMLShort i2) {
        return new JMLShort((short)(shortValue + i2.shortValue));
    }

    /** Return a new object containing the difference between this object's
     *  short value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theShort == \nowarn_op((short)(theShort - i2.theShort));
      @*/
    public /*@ non_null @*/ JMLShort minus(/*@ non_null @*/ JMLShort i2) {
        return new JMLShort((short)(shortValue - i2.shortValue));
    }


    /** Return a new object containing the product of this object's
     * short value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theShort == \nowarn_op((short)(theShort * i2.theShort));
      @*/
    public /*@ non_null @*/ JMLShort times(/*@ non_null @*/ JMLShort i2) {
        return new JMLShort((short)(shortValue * i2.shortValue));
    }

    /** Return a new object containing the quotient of this object's
     *  short value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && !i2.equals(new JMLShort((short)0));
      @    ensures \result != null
      @         && \result.theShort == \nowarn_op((short)(theShort / i2.theShort));
      @*/
    public /*@ non_null @*/ JMLShort dividedBy(/*@ non_null @*/ JMLShort i2) {
        return new JMLShort((short)(shortValue / i2.shortValue));
    }

    //@ axiom (\forall JMLShort i2; i2.equals(new JMLShort((short)0)) <==> i2.theShort == 0);

    /** Return a new object containing the remainder of this object's
     *  short value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && !i2.equals(new JMLShort((short)0));
      @    ensures \result != null
      @         && \result.theShort == theShort % i2.theShort;
      @    // theShort % i2.theShort will always be a short.
      @*/
    public /*@ non_null @*/
        JMLShort remainderBy(/*@ non_null @*/ JMLShort i2) {
        return new JMLShort((short)(shortValue % i2.shortValue));
    }

    /** Tell whether this object's short value is strictly greater
     *  than that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theShort > i2.theShort;
      @*/
    public boolean greaterThan(/*@ non_null */ JMLShort i2) {
        return shortValue > i2.shortValue;
    }

    /** Tell whether this object's short value is strictly less
     *  than that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theShort < i2.theShort;
      @*/
    public boolean lessThan(/*@ non_null */ JMLShort i2) {
        return shortValue < i2.shortValue;
    }

    /** Tell whether this object's short value is greater than or equal
     *  to that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theShort >= i2.theShort;
      @*/
    public boolean greaterThanOrEqualTo(/*@ non_null */ JMLShort i2) {
        return shortValue >= i2.shortValue;
    }

    /** Tell whether this object's short value is less than or equal
     *  to that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theShort <= i2.theShort;
      @*/
    public boolean lessThanOrEqualTo(/*@ non_null */ JMLShort i2) {
        return shortValue <= i2.shortValue;
    }
   
    /** Return a string representation of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null && \result.equals(getShort().toString());
      @*/
    public String toString() {
        return String.valueOf(shortValue);
    }
    
}
