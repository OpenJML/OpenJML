// @(#)$Id: JMLString.java,v 1.24 2007/02/08 14:05:50 leavens Exp $

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

/** A reflection of {@link java.lang.String} that implements {@link JMLType}.
 *
 * @version $Revision: 1.24 $
 * @author Gary T. Leavens
 * @see java.lang.String
 * @see JMLType
 */
//-@ immutable
public /*@ pure @*/ class JMLString implements JMLComparable {

    /** The contents of this object.
     */
    //@ public model String theString;

    //@ public invariant theString != null;

    protected String str_;
    //@               in theString;
    //@ protected represents theString <- str_;

    //@ protected invariant str_ != null;

    //@ public    invariant owner == null;

    /** Initialize the contents of this object to be the empty string.
     * @see #EMPTY
     */
    /*@  public normal_behavior
      @    assignable theString, owner;
      @    ensures theString.equals("");
      @*/
    public JMLString() {
        str_ = "";
        //@ set owner = null;
    }

    /** Initialize the contents of this object to be the given string.
     */
    /*@  public normal_behavior
      @    requires s != null;
      @    assignable theString, owner;
      @    ensures theString.equals(s);
      @*/
    public JMLString(/*@ non_null @*/ String s)
        throws IllegalArgumentException
    {
        if (s != null) {
            str_ = s;
            //@ set owner = null;
        } else {
            throw new IllegalArgumentException();
        }
    }

    /** The empty JMLString.
     * @see #JMLString()
     */
    public static final JMLString EMPTY = new JMLString();

    /** Return a clone of this string.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result == this;
      @*/
    public Object clone() {
        return this;
    }

    /** Compare this to op2, returning a comparison code.
     * @param op2 the object this is compared to.
     * @exception ClassCastException when o is not a JMLString.
     * @exception NullPointerException when o is null.
     * @see #equals(Object)
     * @see #compareTo(JMLString)
     */
    /*@ also
      @   public normal_behavior
      @    requires op2 instanceof JMLString;
      @    ensures \result == theString.compareTo(((JMLString)op2).theString);
      @ also
      @   public exceptional_behavior
      @    requires op2 == null;
      @    requires_redundantly !(op2 instanceof JMLString);
      @    signals_only NullPointerException;
      @ also
      @   public exceptional_behavior
      @    requires op2 != null && !(op2 instanceof JMLString);
      @    signals_only ClassCastException;
      @*/
    public int compareTo(/*@ non_null @*/ Object op2)
           throws ClassCastException, NullPointerException {
        return str_.compareTo(((JMLString)op2).str_); //@ nowarn Cast;
    }

    /** Compares this to another.
     * @see #equals(Object)
     * @see #compareTo(Object)
     */
    /*@ public normal_behavior
      @    requires another != null;
      @    ensures \result == theString.compareTo(another.theString);
      @*/
    public int compareTo(/*@ non_null @*/ JMLString another) {
        return str_.compareTo(another.str_);
    }

    /** Tell if these two strings are equal.
     * @see #equalsIgnoreCase(String)
     * @see #equalsIgnoreCase(JMLString)
     * @see #compareTo(Object)
     * @see #compareTo(JMLString)
     */
    /*@ also
      @  public normal_behavior
      @  {|
      @    requires s != null && s instanceof JMLString;
      @    ensures \result == ((JMLString) s).theString.equals(theString);
      @   also
      @    requires s == null || !(s instanceof JMLString);
      @    ensures !\result;
      @  |}
      @*/
    public boolean equals(/*@ nullable @*/ Object s) {
        if (s != null && s instanceof JMLString) {
            return(str_.equals(((JMLString)s).str_));
        }
        else {
            return(false);
        }
    }

    /** Are these strings equal, except for case?
     * @see #equals
     * @see #equalsIgnoreCase(String)
     * @see #compareTo(Object)
     * @see #compareTo(JMLString)
     */
    /*@ public normal_behavior
      @    requires another != null;
      @    ensures \result == theString.equalsIgnoreCase(another.theString);
      @*/
    public boolean equalsIgnoreCase(/*@ non_null @*/ JMLString another) {
        return str_.equalsIgnoreCase(another.str_);
    }

    /** Are these strings equal, except for case?
     * @see #equals
     * @see #equalsIgnoreCase(JMLString)
     * @see #compareTo(Object)
     * @see #compareTo(JMLString)
     */
    /*@ public normal_behavior
      @    requires another != null;
      @    ensures \result == theString.equalsIgnoreCase(another);
      @*/
    public boolean equalsIgnoreCase(/*@ non_null @*/ String another) {
        return str_.equalsIgnoreCase(another);
    }

    /** Return a hash code for this object.
     */
    // specification is inherited
    public int hashCode() {
        return(str_.hashCode());
    }

    /** Return theString.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result.equals(theString);
      @*/
    public String toString() {
        return(str_);
    }

    /** Produce a new JMLString that is the concatentation of two JMLStrings.
     */
    public JMLString concat(JMLString s) {
	return new JMLString(str_ + s.str_);
    }

    /** Produce a new JMLString that is the concatentation of the JMLString
	and a String.
     */
    public JMLString concat(String s) {
	return new JMLString(str_ + s);
    }

    /** Produce a new JMLString that is the concatentation of the JMLString
	and a char.
     */
    public JMLString concat(char c) {
	return new JMLString(str_ + c);
    }
}

