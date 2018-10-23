// @(#)$Id: JMLChar.java,v 1.26 2007/02/08 14:05:50 leavens Exp $

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

/** A reflection of {@link java.lang.Character} that implements {@link
 * JMLType}.
 *
 * @version $Revision: 1.26 $
 * @author Curtis Clifton with extensive input from the JML Seminar
 * at Iowa State University, June-July 1999.
 * @author Gary T. Leavens
 * @see java.lang.Character
 * @see JMLByte
 * @see JMLShort
 * @see JMLInteger
 * @see JMLLong
 * @see JMLString
 * @see JMLType
 */
//+OPENJML@ immutable
public /*@ pure @*/ class JMLChar implements JMLComparable {

    /** The character that is the abstract value of this object.
     */
    //@ public model char theChar;

    protected final char value;
    //@                    in theChar;
    //@ protected represents theChar <- value;
  
    //@ public invariant owner == null;

    //---------------------------------------------------------------------
    // Constructors
    //---------------------------------------------------------------------

    /** Initialize this to contain the null character.
     */
    /*@  public normal_behavior
      @     assignable theChar, owner;
      @     ensures theChar == '\u0000';
      @*/
    public JMLChar ( ) {
        value = '\u0000';
        //@ set owner = null;
    } 

    /** The JMLChar that represents zero.
     */
    public static final JMLChar ZERO = new JMLChar();

    /** Initialize this to contain the given character.
     */
    /*@  public normal_behavior
      @     assignable theChar, owner;
      @     ensures theChar == c;
      @*/
    public JMLChar(char c) {
        value = c;
        //@ set owner = null;
    }

    /** Initialize this to contain the character contained in the
     * given Character.
     */
    /*@  public normal_behavior
      @     requires inChar != null;
      @     assignable theChar, owner;
      @     ensures theChar == inChar.charValue();
      @*/
    public JMLChar(/*@ non_null @*/ Character inChar) {
        value = inChar.charValue();
        //@ set owner = null;
    }
  
    //---------------------------------------------------------------------
    // JMLType methods that are not in Character class
    //---------------------------------------------------------------------

    /** Return a clone of this object.
     */
    /*@ also
      @  public normal_behavior
      @   ensures \result instanceof JMLChar
      @        && ((JMLChar)\result).equals(this);
      @*/
    public Object clone() {
        return this;
    }
  
    //---------------------------------------------------------------------
    // Character.java Methods
    //---------------------------------------------------------------------

    /** Return the character contained in this object.
     */
    /*@  public normal_behavior
      @    ensures \result == theChar;
      @*/
    public char charValue() {
        return value;
    }

    /** Return a Character object containing this object's character.
     */
    /*@  public normal_behavior
      @    ensures \result != null && \result.equals(new Character(theChar));
      @*/
    public Character getChar() {
        return Character.valueOf(value);
    }

    /** Return a hash code for this object.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result >= 0 && (* \result is a hash code for theChar *);
      @*/
    public int hashCode() {
        return value;
    }
  
    /** Compare this to op2, returning a comparison code.
     *  @param op2 the object this is compared to.
     *  @exception ClassCastException when o is not a JMLChar.
     */
    /*@ also
      @   public normal_behavior
      @    requires op2 instanceof JMLChar;
      @    ensures (theChar < ((JMLChar)op2).theChar ==> \result == -1)
      @         && (theChar == ((JMLChar)op2).theChar ==> \result == 0)
      @         && (theChar > ((JMLChar)op2).theChar ==> \result == +1);
      @ also
      @   public exceptional_behavior
      @    requires op2 != null && !(op2 instanceof JMLChar);
      @    signals_only ClassCastException;
      @*/
    public int compareTo(/*@ non_null @*/ Object op2)
            throws NullPointerException, ClassCastException
    {
        if (op2 == null) {
            throw new NullPointerException();
        } else if (op2 instanceof JMLChar) {
            char cv2  = ((JMLChar)op2).value;
            if (value < cv2) {
                return -1;
            } else if (value == cv2) {
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
      @  public normal_behavior
      @    requires (obj != null && obj instanceof JMLChar);
      @    ensures \result <==> ((JMLChar) obj).theChar == theChar;
      @   also
      @    requires obj == null || !(obj instanceof JMLChar);
      @    ensures !\result;
      @*/
    public boolean equals(/*@ nullable @*/ Object obj) {
        return (obj != null && obj instanceof JMLChar)
            && ((JMLChar) obj).value == value;
    }

    /** Return a string representation of this object.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result != null && \result.equals(String.valueOf(theChar));
      @ implies_that
      @  public normal_behavior
      @    ensures \result != null && \result.equals(getChar().toString());
      @*/
    public String toString() {
        return String.valueOf(value);
    }

    //---------------------------------------------------------------------
    // methods that treat a JMLChar as a number
    //---------------------------------------------------------------------

    /** Return the integer corresponding to this character.
     */
    /*@ public normal_behavior
      @    ensures \result == (int) theChar;
      @*/
    public int intValue() {
        return value;
    }

    /** Return a new object containing the sum of this object's
     *  char value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null;
      @    ensures \result.theChar == \nowarn_op((char) (theChar + i2.theChar));
      @*/
    public /*@ non_null @*/ JMLChar plus(/*@ non_null @*/ JMLChar i2) {
        return new JMLChar((char)(value + i2.value));
    }

    /** Return a new object containing the difference between of this object's
     *  char value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null;
      @    ensures \result.theChar == \nowarn_op((char) (theChar - i2.theChar));
      @*/
    public /*@ non_null @*/ JMLChar minus(/*@ non_null @*/ JMLChar i2) {
        return new JMLChar((char)(value - i2.value));
    }

    /** Return a new object containing the product of this object's
     *  char value and that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result != null;
      @    ensures \result.theChar == \nowarn_op((char) (theChar * i2.theChar));
      @*/
    public /*@ non_null @*/ JMLChar times(/*@ non_null @*/ JMLChar i2) {
        return new JMLChar((char)(value * i2.value));
    }

    /** Return a new object containing the quotient of this object's
     *  char value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && i2.theChar != (char) 0;
      @    ensures \result != null;
      @    ensures \result.theChar == \nowarn_op((char) (theChar / i2.theChar));
      @*/
    public /*@ non_null @*/ JMLChar dividedBy(/*@ non_null @*/ JMLChar i2) {
        //@ assume i2.value != 0;
        return new JMLChar((char)(value / i2.value));
    }

    /** Return a new object containing the remainder of this object's
     *  char value divided by that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null && i2.theChar != (char) 0;
      @    ensures \result != null;
      @    ensures \result.theChar == (char) (theChar % i2.theChar);
      @*/
    public /*@ non_null @*/ JMLChar remainderBy(/*@ non_null @*/ JMLChar i2) {
        //@ assume i2.value != 0;
        return new JMLChar((char)(value % i2.value));
    }

    /** Tell whether this this object's char value is strictly greater
     *  than that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theChar > i2.theChar;
      @*/
    public boolean greaterThan(/*@ non_null */ JMLChar i2) {
        return value > i2.value;
    }

    /** Tell whether this this object's char value is strictly less
     *  than that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theChar < i2.theChar;
      @*/
    public boolean lessThan(/*@ non_null */ JMLChar i2) {
        return value < i2.value;
    }

    /** Tell whether this this object's char value is greater
     *  than or equal to that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theChar >= i2.theChar;
      @*/
    public boolean greaterThanOrEqualTo(/*@ non_null */ JMLChar i2) {
        return value >= i2.value;
    }

    /** Tell whether this this object's char value is less
     *  than or equal to that of the given argument.
     */
    /*@  public normal_behavior
      @    requires i2 != null;
      @    ensures \result <==> theChar <= i2.theChar;
      @*/
    public boolean lessThanOrEqualTo(/*@ non_null */ JMLChar i2) {
        return value <= i2.value;
    }
}
