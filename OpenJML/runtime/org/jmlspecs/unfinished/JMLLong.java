// @(#)$Id: JMLLong.java,v 1.24 2007/02/08 14:05:50 leavens Exp $

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

/** A reflection of {@link java.lang.Long} that implements {@link JMLType}.
 *
 * @version $Revision: 1.24 $
 * @author Gary T. Leavens
 * @author Brandon Shilling
 * @see java.lang.Long
 * @see JMLInteger
 * @see JMLShort
 * @see JMLByte
 * @see JMLChar
 * @see JMLType
 */
//+OPENJML@ immutable
public /*@ pure @*/ class JMLLong implements JMLComparable {

    /** The long value of this object.
     */
    //@ public model long theLong;

    //@ public constraint theLong == \old(theLong);

    private long longValue;
    //@             in theLong;
    //@ private represents theLong <- longValue;

    //@ public invariant owner == null;

    /** Initialize this object to 0.
     */
    /*@  public normal_behavior
      @    assignable theLong,owner;
      @    ensures theLong == 0;
      @*/
    public JMLLong ( ) {
        longValue = 0;
        //@ set owner = null;
    } 
   
    /** Initialize this object to the given long.
     */
    /*@  public normal_behavior
      @    assignable theLong, owner;
      @    ensures theLong == inLong;
      @*/
    public JMLLong (long inLong) {
        longValue = inLong;
        //@ set owner = null;
    } 

    /** Initialize this object to the given int.
     */
    /*@  public normal_behavior
      @    assignable theLong, owner;
      @    ensures theLong == inInt;
      @*/
    public JMLLong (int inInt) {
        longValue = (long)inInt;
        //@ set owner = null;
    } 

    /** Initialize this object to the given long.
     *  @param inLong an object containing the value to use.
     */
    /*@  public normal_behavior
      @    requires inLong != null;
      @    assignable theLong, owner;
      @    ensures theLong == inLong.longValue();
      @*/
    public JMLLong(/*@ non_null */ Long inLong) {
        longValue = inLong.longValue();
        //@ set owner = null;
    }

    /** Initialize this object to the given long.
     *  @param s a string that contains the decimal representation of
     *  the desired value.
     */
    /*@  public behavior
      @    requires s != null
      @          && (* s is a properly formatted long literal *);
      @    assignable theLong, owner;
      @    ensures theLong == (new Long(s)).longValue();
      @*/
    public JMLLong (/*@ non_null @*/ String s) throws JMLTypeException {
        //@ set owner = null;
        try {
            longValue = Long.valueOf(s).longValue();
        } catch (RuntimeException re) {
            throw new JMLTypeException("Bad format string passed to "
                                       + "JMLLong(String): \""
                                       + s + "\"");
        }
    }

    /** The JMLLong that represents zero.
     */
    public static final JMLLong ZERO = new JMLLong();
   
    /** The JMLLong that represents one.
     */
    public static final JMLLong ONE = new JMLLong(1);

    /** Return a clone of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof JMLLong
      @     	  && ((JMLLong)\result).theLong == theLong;
      @*/
    public Object clone() {
        return this;
    }
   
    /** Compare this to op2, returning a comparison code.
     *  @param op2 the object this is compared to.
     *  @exception ClassCastException when o is not a JMLLong.
     */
    /*@ also
      @   public normal_behavior
      @    requires op2 instanceof JMLLong;
      @    ensures (theLong < ((JMLLong)op2).theLong ==> \result == -1)
      @         && (theLong == ((JMLLong)op2).theLong ==> \result == 0)
      @         && (theLong > ((JMLLong)op2).theLong ==> \result == +1);
      @ also
      @   public exceptional_behavior
      @    requires op2 != null && !(op2 instanceof JMLLong);
      @    signals_only ClassCastException;
      @*/
    public int compareTo(/*@ non_null @*/ Object op2) throws ClassCastException {
        if (op2 instanceof JMLLong) {
            long lv2 = ((JMLLong)op2).longValue;
            if (longValue < lv2) {
                return -1;
            } else if (longValue == lv2) {
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
      @     ensures \result <==> op2 != null && op2 instanceof JMLLong 
      @                          && theLong == ((JMLLong)op2).theLong;
      @*/
    public boolean equals(/*@ nullable @*/ Object op2) {
        return op2 != null && op2 instanceof JMLLong
            && longValue == ((JMLLong)op2).longValue;
    } 

    /** Return a hash code for this object.
     */
    public /*@ pure @*/ int hashCode() {
        return (int) longValue;
    }

    /** Return the long value in this object.
     */
    /*@  public normal_behavior
      @    ensures \result == theLong;
      @*/
    public long longValue() {
        return longValue;
    }

    /** Return an Long object containing the long value in this
     * object.
     */
    /*@  public normal_behavior
      @    ensures \result != null && \result.equals(new Long(theLong));
      @*/
    public /*@ non_null @*/ Long getLong() {
        return new Long(longValue);
    }

    /** Return a new object containing the negation of this object's
     * long value.
     */
    /*@  public normal_behavior
      @    ensures \result != null && \result.theLong == \nowarn(- theLong);
      @*/
    public /*@ non_null @*/ JMLLong negated() {
        return new JMLLong(- longValue);
    }

    /** Return a new object containing the sum of this object's
     *  long value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theLong == \nowarn(theLong + i2.theLong);
      @*/
    public /*@ non_null @*/ JMLLong plus(/*@ non_null @*/ JMLLong i2) {
        return new JMLLong(longValue + i2.longValue);
    }

    /** Return a new object containing the difference between this object's
     *  long value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theLong == \nowarn(theLong - i2.theLong);
      @*/
    public /*@ non_null @*/ JMLLong minus(/*@ non_null @*/ JMLLong i2) {
        return new JMLLong(longValue - i2.longValue);
    }


    /** Return a new object containing the product of this object's
     * long value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theLong == \nowarn(theLong * i2.theLong);
      @*/
    public /*@ non_null @*/ JMLLong times(/*@ non_null @*/ JMLLong i2) {
        return new JMLLong(longValue * i2.longValue);
    }

    /** Return a new object containing the quotient of this object's
     *  long value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && !i2.equals(new JMLLong(0));
      @    ensures \result != null
      @         && \result.theLong == \nowarn(theLong / i2.theLong);
      @*/
    public /*@ non_null @*/ JMLLong dividedBy(/*@ non_null @*/ JMLLong i2) {
        //@ assume i2.longValue != 0;
        return new JMLLong(longValue / i2.longValue);
    }

    /** Return a new object containing the remainder of this object's
     *  long value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && !i2.equals(new JMLLong(0));
      @    ensures \result != null
      @         && \result.theLong == theLong % i2.theLong;
      @*/
    public /*@ non_null @*/
        JMLLong remainderBy(/*@ non_null @*/ JMLLong i2) {
        //@ assume i2.longValue != 0;
        return new JMLLong(longValue % i2.longValue);
    }

    /** Tell whether this object's long value is strictly greater
     *  than that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theLong > i2.theLong;
      @*/
    public boolean greaterThan(/*@ non_null */ JMLLong i2) {
        //@ assume i2 != null;
        return longValue > i2.longValue;
    }

    /** Tell whether this object's long value is strictly less
     *  than that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theLong < i2.theLong;
      @*/
    public boolean lessThan(/*@ non_null */ JMLLong i2) {
        //@ assume i2 != null;
        return longValue < i2.longValue;
    }

    /** Tell whether this object's long value is greater than or equal
     *  to that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theLong >= i2.theLong;
      @*/
    public boolean greaterThanOrEqualTo(/*@ non_null */ JMLLong i2) {
        //@ assume i2 != null;
        return longValue >= i2.longValue;
    }

    /** Tell whether this object's long value is less than or equal
     *  to that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theLong <= i2.theLong;
      @*/
    public boolean lessThanOrEqualTo(/*@ non_null */ JMLLong i2) {
        //@ assume i2 != null;
        return longValue <= i2.longValue;
    }
   
    /** Return a string representation of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null && \result.equals(getLong().toString());
      @*/
    public String toString() {
        return String.valueOf(longValue);
    }
    
}
