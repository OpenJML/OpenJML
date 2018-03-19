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
public @Pure class JMLByte implements JMLComparable<JMLByte> {

    private static final long serialVersionUID = 769042189784802260L;

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
      @    ensures theByte == Byte.parseByte(s);
      @*/
    public JMLByte (@NonNull  String s) throws JMLTypeException {
        //@ set owner = null;
        try {
            byteValue = Byte.parseByte(s);
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
    @NonNull 
    public Object clone() {
        return this;
    }
   
    /** Compare this to op2, returning a comparison code.
     *  @param op2 the object this is compared to.
     */
  /*@ also
  @   public normal_behavior
  @    ensures (theByte < op2.theByte ==> \result == -1)
  @         && (theByte == op2.theByte ==> \result == 0)
  @         && (theByte > op2.theByte ==> \result == +1);
  @ also
  @   public exceptional_behavior
  @    requires op2 != null && !(op2 instanceof JMLByte);
  @    signals_only ClassCastException;
  @*/
  public int compareTo(@NonNull JMLByte op2) throws ClassCastException {
      byte bv2 = op2.byteValue;
      if (byteValue < bv2) {
          return -1;
      } else if (byteValue == bv2) {
          return 0;
      } else {
          return +1;
      }
  }

    /** Test whether this object's value is equal to the given argument.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result <==> op2 != null && op2 instanceof JMLByte 
      @                          && theByte == ((JMLByte)op2).theByte;
      @*/
    public boolean equals(@Nullable Object op2) {
        return op2 != null && op2 instanceof JMLByte
            && byteValue == ((JMLByte)op2).byteValue;
    } 

    /** Return a hash code for this object.
     */
    public int hashCode() {
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
    public @NonNull Byte getByte() {
        return new Byte(byteValue);
    }

    /** Return a new object containing the negation of this object's
     * byte value.
     */
    /*@  public normal_behavior
      @    ensures \result != null && 
      @      \result.theByte == \nowarn_op((byte)- theByte);
      @*/
    public @NonNull JMLByte negated() {
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
    public @NonNull JMLByte plus(@NonNull JMLByte i2) {
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
    public @NonNull JMLByte minus(@NonNull JMLByte i2) {
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
    public @NonNull JMLByte times(@NonNull JMLByte i2) {
        return new JMLByte((byte)(byteValue * i2.byteValue));
    }

    /** Return a new object containing the quotient of this object's
     *  byte value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && !i2.equals(ZERO);
      @    ensures \result != null
      @         && \result.theByte == \nowarn_op((byte)(theByte / i2.theByte));
      @*/
    public @NonNull JMLByte dividedBy(@NonNull JMLByte i2) {
        //@ assume i2.byteValue != 0;
        return new JMLByte((byte)(byteValue / i2.byteValue));
    }

    /** Return a new object containing the remainder of this object's
     *  byte value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && !i2.equals(ZERO);
      @    ensures \result != null
      @         && \result.theByte == theByte % i2.theByte;
      @    // theByte % i2.theByte will always fit within a byte.
      @*/
    public @NonNull
        JMLByte remainderBy(@NonNull JMLByte i2) {
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
    public boolean greaterThan(@NonNull JMLByte i2) {
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
    public boolean lessThan(@NonNull JMLByte i2) {
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
    public boolean greaterThanOrEqualTo(@NonNull JMLByte i2) {
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
    public boolean lessThanOrEqualTo(@NonNull JMLByte i2) {
        //@ assume i2 != null;
        return byteValue <= i2.byteValue;
    }
   
    /** Return a string representation of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null && \result.equals(getByte().toString());
      @*/
    public @NonNull String toString() {
        return String.valueOf(byteValue);
    }
    
}
