// @(#)$Id: JMLByte.java,v 1.27 2007/02/08 14:05:50 leavens Exp $

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

/** A reflection of {@link java.lang.Byte} that implements {@link JMLType}.
 *
 * @version $Revision: 1.27 $
 * @author Gary T. Leavens
 * @author Brandon Shilling
 * @see java.lang.Byte
 * @see JMLType
 * @see JMLChar
 * @see JMLInteger
 * @see JMLShort
 * @see JMLLong
 */
//+OPENJML@ immutable
public /*@ pure @*/ class JMLByte implements JMLComparable {

    /** The byte value of this object.
     */
    //@ public model byte theByte;

    //@ public constraint theByte == \old(theByte);

    private byte byteValue;
    //@             in theByte;
    //@ private represents theByte <- byteValue;

    //@ public invariant owner == null;

    /** Initialize this object to 0.
     */
    /*@  public normal_behavior
      @    assignable theByte, owner;
      @    ensures theByte == 0;
      @*/
    public JMLByte ( ) {
        byteValue = 0;
        //@ set owner = null;
    } 

    /** Initialize this object to the given byte.
     */
    /*@  public normal_behavior
      @    assignable theByte, owner;
      @    ensures theByte == inByte;
      @*/
    public JMLByte (byte inByte) {
        byteValue = inByte;
        //@ set owner = null;
    } 

    /** Initialize this object to the given byte.
     *  @param inByte an object containing the value to use.
     */
    /*@  public normal_behavior
      @    requires inByte != null;
      @    assignable theByte, owner;
      @    ensures theByte == inByte.byteValue();
      @*/
    public JMLByte(/*@ non_null */ Byte inByte) {
        byteValue = inByte.byteValue();
        //@ set owner = null;
    }

    /** Initialize this object to the given byte.
     *  @param s a string that contains the decimal representation of
     *  the desired value.
     */
    /*@  public behavior
      @    requires s != null
      @          && (* s is a properly formatted byte literal *);
      @    assignable theByte, owner;
      @    ensures theByte == (new Byte(s)).byteValue();
      @*/
    public JMLByte (/*@ non_null @*/ String s) throws JMLTypeException {
        //@ set owner = null;
        try {
            byteValue = Byte.valueOf(s).byteValue(); //@ nowarn Null;
        } catch (RuntimeException re) {
            throw new JMLTypeException("Bad format string passed to "
                                       + "JMLByte(String): \""
                                       + s + "\"");
        }
    }
   
    /** The JMLByte that represents zero.
     */
    public static final JMLByte ZERO = new JMLByte();
   
    /** The JMLByte that represents one.
     */
    public static final JMLByte ONE = new JMLByte((byte)1);

    /** Return a clone of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof JMLByte
      @     	  && ((JMLByte)\result).theByte == theByte;
      @*/
    public Object clone() {
        return this;
    }
   
    /** Compare this to op2, returning a comparison code.
     *  @param op2 the object this is compared to.
     *  @exception ClassCastException when o is not a JMLByte.
     */
    /*@ also
      @   public normal_behavior
      @    requires op2 instanceof JMLByte;
      @    ensures (theByte < ((JMLByte)op2).theByte ==> \result == -1)
      @         && (theByte == ((JMLByte)op2).theByte ==> \result == 0)
      @         && (theByte > ((JMLByte)op2).theByte ==> \result == +1);
      @ also
      @   public exceptional_behavior
      @    requires op2 != null && !(op2 instanceof JMLByte);
      @    signals_only ClassCastException;
      @*/
    public int compareTo(/*@ non_null @*/ Object op2) throws ClassCastException {
        if (op2 instanceof JMLByte) {
            byte bv2 = ((JMLByte)op2).byteValue;
            if (byteValue < bv2) {
                return -1;
            } else if (byteValue == bv2) {
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
      @     ensures \result <==> op2 != null && op2 instanceof JMLByte 
      @                          && theByte == ((JMLByte)op2).theByte;
      @*/
    public boolean equals(/*@ nullable @*/ Object op2) {
        return op2 != null && op2 instanceof JMLByte
            && byteValue == ((JMLByte)op2).byteValue;
    } 

    /** Return a hash code for this object.
     */
    public /*@ pure @*/ int hashCode() {
        return byteValue;
    }

    /** Return the byte value in this object.
     */
    /*@  public normal_behavior
      @    ensures \result == theByte;
      @*/
    public byte byteValue() {
        return byteValue;
    }

    /** Return an Byte object containing the byte value in this
     * object.
     */
    /*@  public normal_behavior
      @    ensures \result != null && \result.equals(new Byte(theByte));
      @*/
    public /*@ non_null @*/ Byte getByte() {
        return Byte.valueOf(byteValue);
    }

    /** Return a new object containing the negation of this object's
     * byte value.
     */
    /*@  public normal_behavior
      @    ensures \result != null && 
      @      \result.theByte == \nowarn_op((byte)- theByte);
      @*/
    public /*@ non_null @*/ JMLByte negated() {
        return new JMLByte((byte) - byteValue);
    }

    /** Return a new object containing the sum of this object's
     *  byte value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theByte == \nowarn_op((byte)(theByte + i2.theByte));
      @*/
    public /*@ non_null @*/ JMLByte plus(/*@ non_null @*/ JMLByte i2) {
        return new JMLByte((byte)(byteValue + i2.byteValue));
    }

    /** Return a new object containing the difference between this object's
     *  byte value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theByte == \nowarn_op((byte)(theByte - i2.theByte));
      @*/
    public /*@ non_null @*/ JMLByte minus(/*@ non_null @*/ JMLByte i2) {
        return new JMLByte((byte)(byteValue - i2.byteValue));
    }


    /** Return a new object containing the product of this object's
     * byte value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null
      @         && \result.theByte == \nowarn_op((byte)(theByte * i2.theByte));
      @*/
    public /*@ non_null @*/ JMLByte times(/*@ non_null @*/ JMLByte i2) {
        return new JMLByte((byte)(byteValue * i2.byteValue));
    }

    /** Return a new object containing the quotient of this object's
     *  byte value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && !i2.equals(new JMLByte((byte)0));
      @    ensures \result != null
      @         && \result.theByte == \nowarn_op((byte)(theByte / i2.theByte));
      @*/
    public /*@ non_null @*/ JMLByte dividedBy(/*@ non_null @*/ JMLByte i2) {
        //@ assume i2.byteValue != 0;
        return new JMLByte((byte)(byteValue / i2.byteValue));
    }

    /** Return a new object containing the remainder of this object's
     *  byte value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && !i2.equals(new JMLByte((byte)0));
      @    ensures \result != null
      @         && \result.theByte == theByte % i2.theByte;
      @    // theByte % i2.theByte will always fit within a byte.
      @*/
    public /*@ non_null @*/
        JMLByte remainderBy(/*@ non_null @*/ JMLByte i2) {
        //@ assume i2.byteValue != 0;
        return new JMLByte((byte)(byteValue % i2.byteValue));
    }

    /** Tell whether this object's byte value is strictly greater
     *  than that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theByte > i2.theByte;
      @*/
    public boolean greaterThan(/*@ non_null */ JMLByte i2) {
        //@ assume i2 != null;
        return byteValue > i2.byteValue;
    }

    /** Tell whether this object's byte value is strictly less
     *  than that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theByte < i2.theByte;
      @*/
    public boolean lessThan(/*@ non_null */ JMLByte i2) {
        //@ assume i2 != null;
        return byteValue < i2.byteValue;
    }

    /** Tell whether this object's byte value is greater than or equal
     *  to that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theByte >= i2.theByte;
      @*/
    public boolean greaterThanOrEqualTo(/*@ non_null */ JMLByte i2) {
        //@ assume i2 != null;
        return byteValue >= i2.byteValue;
    }

    /** Tell whether this object's byte value is less than or equal
     *  to that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theByte <= i2.theByte;
      @*/
    public boolean lessThanOrEqualTo(/*@ non_null */ JMLByte i2) {
        //@ assume i2 != null;
        return byteValue <= i2.byteValue;
    }
   
    /** Return a string representation of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null && \result.equals(getByte().toString());
      @*/
    public String toString() {
        return String.valueOf(byteValue);
    }
    
}
