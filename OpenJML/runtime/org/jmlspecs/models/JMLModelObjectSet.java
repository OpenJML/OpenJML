// @(#)$Id: JMLModelObjectSet.java,v 1.13 2005/07/07 21:03:07 leavens Exp $

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

/** A collection of object sets for use in set comprehensions.  All of
 * the public methods are model methods, because there is no way to
 * compute the set of all potential object identities of any given
 * type.
 *
 * <p> This type is not that useful, as you can mostly just use
 * quantification over the relevant type instead of one of these sets.
 * Indeed the sets are defined by using universal quantifiers, and so their
 * use is roughly equivalent.
 *
 * @version $Revision: 1.13 $
 * @author Gary T. Leavens
 */
//-@ immutable
public /*@ pure @*/ class JMLModelObjectSet {

    /** This class has no instances.
     */
    private JMLModelObjectSet() {}

    /** The set of all (actual and potential) JMLByte objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLByte x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLBytes();
    @*/

    /** The set of all (actual and potential) JMLChar objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLChar x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLChars();
    @*/

    /** The set of all (actual and potential) JMLInteger objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLInteger x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLIntegers();
    @*/

    /** The set of all (actual and potential) JMLLong objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLLong x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLLongs();
    @*/

    /** The set of all (actual and potential) JMLShort objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLShort x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLShorts();
    @*/

    /** The set of all (actual and potential) JMLString objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLString x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLStrings();
    @*/

    /** The set of all (actual and potential) JMLFloat objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLFloat x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLFloats();
    @*/

    /** The set of all (actual and potential) JMLDouble objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
      @    ensures (\forall JMLDouble x; ; \result.has(x));
    public static pure model non_null JMLObjectSet JMLDoubles();
    @*/

    /** The set of all (actual and potential) Boolean objects.
     */
    /*@ public normal_behavior
      @    assignable \nothing;
     @     ensures (\forall Boolean x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Booleans();
    @*/

    /** The set of all (actual and potential) Byte objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Byte x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Bytes();
    @*/

    /** The set of all (actual and potential) Character objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Character x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Characters();
    @*/

    /** The set of all (actual and potential) Integer objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Integer x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Integers();
    @*/

    /** The set of all (actual and potential) Long objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Long x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Longs();
    @*/

    /** The set of all (actual and potential) Short objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Short x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Shorts();
    @*/

    /** The set of all (actual and potential) String objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall String x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Strings();
    @*/

    /** The set of all (actual and potential) Float objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Float x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Floats();
    @*/

    /** The set of all (actual and potential) Double objects.
     */
    /*@ public normal_behavior
     @     assignable \nothing;
     @     ensures (\forall Double x; ; \result.has(x));
    public static pure model non_null JMLObjectSet Doubles();
    @*/
}

