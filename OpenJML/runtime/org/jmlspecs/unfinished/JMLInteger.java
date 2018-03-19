// @(#)$Id: JMLInteger.java,v 1.24 2007/02/08 14:05:50 leavens Exp $

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

/** A reflection of {@link java.lang.Integer} that implements {@link JMLType}.
 *
 * @version $Revision: 1.24 $
 * @author Gary T. Leavens
 * @author Brandon Shilling
 * @see java.lang.Integer
 * @see JMLLong
 * @see JMLShort
 * @see JMLByte
 * @see JMLChar
 * @see JMLType
 */
//+OPENJML@ immutable
public /*@ pure @*/ class JMLInteger implements JMLComparable {

    /** The integer value of this object. */
    //@ public model int theInt;

    //@ public constraint theInt == \old(theInt);

    private int intValue;
    //@            in theInt;
    //@ private represents theInt <- intValue;

    //@ public invariant owner == null;

    /** Initialize this object to 0.
     */
    /*@  public normal_behavior
      @    assignable theInt, owner;
      @    ensures theInt == 0;
      @*/
    public JMLInteger ( ) {
        intValue = 0;
        //@ set owner = null;
    } 
   
    /** Initialize this object to the given int.
     */
    /*@  public normal_behavior
      @    assignable theInt, owner;
      @    ensures theInt == inInt;
      @*/
    public JMLInteger (int inInt) {
        intValue = inInt;
        //@ set owner = null;
    } 

    /** Initialize this object to the given Integer's value.
     *  @param inInteger an object containing the value to use.
     */
    /*@  public normal_behavior
      @    requires inInteger != null;
      @    assignable theInt, owner;
      @    ensures theInt == inInteger.intValue();
      @*/
    public JMLInteger(/*@ non_null */ Integer inInteger) {
        intValue = inInteger.intValue();
        //@ set owner = null;
    }

    /** Initialize this object to the given integer.
     *  @param s a string that contains the decimal representation of
     *  the desired value.
     */
    /*@  public behavior
      @    requires s != null
      @          && (* s is a properly formatted int literal *);
      @    assignable theInt, owner;
      @    ensures theInt == (new Integer(s)).intValue();
      @*/
    public JMLInteger (/*@ non_null @*/ String s) throws JMLTypeException {
        //@ set owner = null;
        try {
            intValue = Integer.valueOf(s).intValue();
        } catch (RuntimeException re) {
            throw new JMLTypeException("Bad format string passed to "
                                       + "JMLInteger(String): \""
                                       + s + "\"");
        }
    }

    /** The JMLInteger that represents zero.
     */
    public static final JMLInteger ZERO = new JMLInteger();

    /** The JMLInteger that represents one.
     */
    public static final JMLInteger ONE = new JMLInteger(1);


    /** Return a clone of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof JMLInteger
      @     	 && ((JMLInteger)\result).theInt == theInt;
      @*/
    public Object clone() {
        return this;
    }
   
    /** Compare this to op2, returning a comparison code.
     *  @param op2 the object this is compared to.
     *  @exception ClassCastException when o is not a JMLInteger.
     */
    /*@ also
      @   public normal_behavior
      @    requires op2 instanceof JMLInteger;
      @    ensures (theInt < ((JMLInteger)op2).theInt ==> \result == -1)
      @         && (theInt == ((JMLInteger)op2).theInt ==> \result == 0)
      @         && (theInt > ((JMLInteger)op2).theInt ==> \result == +1);
      @ also
      @   public exceptional_behavior
      @    requires op2 != null && !(op2 instanceof JMLInteger);
      @    signals_only ClassCastException;
      @*/
    public int compareTo(/*@ non_null @*/ Object op2) 
            throws NullPointerException, ClassCastException
    {
        if (op2 == null) {
            throw new NullPointerException();
        } else if (op2 instanceof JMLInteger) {
            int iv2 = ((JMLInteger)op2).intValue;
            if (intValue < iv2) {
                return -1;
            } else if (intValue == iv2) {
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
      @     ensures \result <==> op2 != null && op2 instanceof JMLInteger 
      @                          && theInt == ((JMLInteger)op2).theInt;
      @*/
    public boolean equals(/*@ nullable @*/ Object op2) {
        return op2 != null && op2 instanceof JMLInteger
            && intValue == ((JMLInteger)op2).intValue;
    } 

    /** Return a hash code for this object.
     */
    public /*@ pure @*/ int hashCode() {
        return intValue;
    }

    /** Return the integer value in this object.
     */
    /*@  public normal_behavior
      @    ensures \result == theInt;
      @*/
    public int intValue() {
        return intValue;
    }

    /** Return an Integer object containing the integer value in this
     * object.
     */
    /*@  public normal_behavior
      @    ensures \result != null && \result.equals(new Integer(theInt));
      @*/
    public /*@ non_null @*/ Integer getInteger() {
        return new Integer(intValue);
    }

    /** Return a new object containing the negation of this object's
     * integer value.
     */
    /*@  public normal_behavior
      @    ensures \result != null && \result.theInt == \nowarn_op(- theInt);
      @*/
    public /*@ non_null @*/ JMLInteger negated() {
        return new JMLInteger(- intValue);
    }

    /** Return a new object containing the sum of this object's
     *  integer value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theInt == \nowarn_op(theInt + i2.theInt);
      @*/
    public /*@ non_null @*/ JMLInteger plus(/*@ non_null @*/ JMLInteger i2) {
        return new JMLInteger(intValue + i2.intValue);
    }

    /** Return a new object containing the difference between this object's
     *  integer value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theInt == \nowarn_op(theInt - i2.theInt);
      @*/
    public /*@ non_null @*/ JMLInteger minus(/*@ non_null @*/ JMLInteger i2) {
        return new JMLInteger(intValue - i2.intValue);
    }


    /** Return a new object containing the product of this object's
     * integer value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theInt == \nowarn_op(theInt * i2.theInt);
      @*/
    public /*@ non_null @*/ JMLInteger times(/*@ non_null @*/ JMLInteger i2) {
        return new JMLInteger(intValue * i2.intValue);
    }

    /** Return a new object containing the quotient of this object's
     *  integer value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && !i2.equals(new JMLInteger(0));
      @    ensures \result != null
      @         && \result.theInt == \nowarn_op(theInt / i2.theInt);
      @*/
    public /*@ non_null @*/
        JMLInteger dividedBy(/*@ non_null @*/ JMLInteger i2) {
        //@ assume i2.intValue != 0;
        return new JMLInteger(intValue / i2.intValue);
    }

    /** Return a new object containing the remainder of this object's
     *  integer value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && !i2.equals(new JMLInteger(0));
      @    ensures \result != null
      @         && \result.theInt == theInt % i2.theInt;
      @*/
    public /*@ non_null @*/
        JMLInteger remainderBy(/*@ non_null @*/ JMLInteger i2) {
        //@ assume i2.intValue != 0;
        return new JMLInteger(intValue % i2.intValue);
    }

    /** Tell whether this object's integer value is strictly greater
     *  than that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theInt > i2.theInt;
      @*/
    public boolean greaterThan(/*@ non_null */ JMLInteger i2) {
        //@ assume i2 != null;
        return intValue > i2.intValue;
    }

    /** Tell whether this object's integer value is strictly less
     *  than that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theInt < i2.theInt;
      @*/
    public boolean lessThan(/*@ non_null */ JMLInteger i2) {
        //@ assume i2 != null;
        return intValue < i2.intValue;
    }

    /** Tell whether this object's integer value is greater than or equal
     *  to that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theInt >= i2.theInt;
      @*/
    public boolean greaterThanOrEqualTo(/*@ non_null */ JMLInteger i2) {
        //@ assume i2 != null;
        return intValue >= i2.intValue;
    }

    /** Tell whether this object's integer value is less than or equal
     *  to that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theInt <= i2.theInt;
      @*/
    public boolean lessThanOrEqualTo(/*@ non_null */ JMLInteger i2) {
        //@ assume i2 != null;
        return intValue <= i2.intValue;
    }
   
    /** Return a string representation of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null && \result.equals(getInteger().toString());
      @*/
    public String toString() {
        return String.valueOf(intValue);
    }
    
}
