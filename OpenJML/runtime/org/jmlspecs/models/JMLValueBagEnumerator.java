// @(#)$Id: JMLBagEnumerator.java-generic,v 1.42 2005/12/24 21:20:31 chalin Exp $

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

import java.util.Enumeration;

/** Enumerators for bags (i.e., multisets) of values.
 *
 * @version $Revision: 1.42 $
 * @author Gary T. Leavens, with help from Albert Baker, Clyde Ruby,
 * and others.
 * @see JMLEnumeration
 * @see JMLType
 * @see JMLValueBag
 * @see JMLEnumerationToIterator
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class JMLValueBagEnumerator
    implements JMLEnumeration, JMLValueType
{
    /** The elements that have not yet been returned by nextElement.
     */
    //@ public model JMLValueBag uniteratedElems;   in objectState;

    /** The bag underlying this enumerator.
     */
    protected /*@ non_null @*/ JMLValueBag currentBag;
    //@                                        in uniteratedElems;

    /** The remaining count of repetitions that the current entry
     * should be returned.
     */
    protected int currentCount;
    //@                 in uniteratedElems;

    /** The current entry.
     */
    protected JMLType currEntry;
    //@                     in uniteratedElems;

    /*@ protected represents
      @     uniteratedElems <- currentBag.removeAll(currEntry)
      @                                  .insert(currEntry, currentCount);
      @*/

    //@ protected invariant currentCount >= 0;

    /*@ protected invariant currentCount > 0
      @            ==> (* currEntry is holds an element, which may be null *);
      @ protected invariant !currentBag.isEmpty()
      @      ==> currentBag.has(currEntry)
      @          && currentCount <= currentBag.count(currEntry);
      @*/

    //@ protected invariant currentCount > 0 ==> moreElements;
    /*@ protected invariant moreElements <==>
      @               (currentCount > 0 || !currentBag.isEmpty());
      @*/

    //@ public invariant elementType <: \type(JMLType);

    /*@ public invariant
      @       !uniteratedElems.isEmpty()
      @        ==> uniteratedElems.elementType <: elementType;
      @*/

    //@ public constraint returnsNull == \old(returnsNull);

    /*@ public invariant
      @       !returnsNull
      @         ==> uniteratedElems.isEmpty() || !uniteratedElems.containsNull;
      @*/

    /** Initialize this with the given bag.
     */
    /*@ normal_behavior
      @   requires b != null;
      @   assignable uniteratedElems;
      @   assignable moreElements, elementType, returnsNull, owner;
      @   ensures uniteratedElems.equals(b);
      @    ensures owner == null;
      @    ensures elementType == b.elementType;
      @    ensures returnsNull == b.containsNull;
      @*/
    JMLValueBagEnumerator(/*@ non_null @*/ JMLValueBag b) {
        //@ set owner = null;
        //@ set elementType = b.elementType;
        //@ set returnsNull = b.containsNull;
        currentBag = b;
        if (!currentBag.isEmpty()) {
            //@ assume currentBag.size > 0;
            currEntry = currentBag.choose();
            currentCount = currentBag.count(currEntry);
            //@ assume currentCount > 0;
            //@ assert !currentBag.isEmpty();
        } else {
            currentCount = 0;
            //@ assert currentBag.isEmpty();
        }
    }

    /** Tells whether this enumerator has more uniterated elements.
     */
    /*@ also
      @   public normal_behavior
      @   ensures \result == !uniteratedElems.isEmpty();
      @   ensures_redundantly \result == moreElements;
      @   ensures_redundantly \result <==> !uniteratedElems.isEmpty();
      @   ensures_redundantly \result <=!=> uniteratedElems.isEmpty();
      @   ensures_redundantly \result != uniteratedElems.isEmpty();
      @*/
    public /*@ pure @*/ boolean hasMoreElements() {
        boolean ret = currentCount > 0 || !currentBag.isEmpty();
        //@ assert ret ==> !uniteratedElems.isEmpty();
        //@ assert uniteratedElems.isEmpty() ==> !ret;
        return ret;
    } //@ nowarn Post;

    /** Return the next element in this, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     */
    /*@ also
      @   public normal_behavior
      @     requires hasMoreElements();
      @     assignable uniteratedElems, moreElements;
      @     ensures \old(uniteratedElems).has((JMLType) \result)
      @       && uniteratedElems.equals(\old(uniteratedElems)
      @             .remove((JMLType) \result));
      @ also
      @   public exceptional_behavior
      @     requires !hasMoreElements();
      @     assignable \nothing;
      @     signals_only JMLNoSuchElementException;
      @*/
    public Object nextElement() throws JMLNoSuchElementException {
        if (currentCount > 0 || !currentBag.isEmpty()) {
            //@ assert !uniteratedElems.isEmpty();
            JMLType retValue;
            if (currEntry == null) {
                retValue = null;
            } else {
                retValue = (JMLType)currEntry.clone();
                //@ assume \typeof(retValue) <: elementType;
            }
            //@ assume retValue == null ==> returnsNull;
            currentCount--;
            if (currentCount <= 0) {
                // The following gratiutious assignment is added because
                // ESC/Java imagines that a callback may happen...
                currentCount = 0;
                currentBag = currentBag.removeAll(currEntry);
                if (currentBag.isEmpty()) {
                    //@ assume currentBag.size == 0;
                    currentCount = 0;
                    //@ assert uniteratedElems.isEmpty();
                } else {
                    //@ assume currentBag.size > 0;
                    currEntry = currentBag.choose();
                    currentCount = currentBag.count(currEntry);
                    //@ assume currentCount > 0;
                    //@ assert !uniteratedElems.isEmpty();
                }
            }
            return retValue;
        } else {
            throw new JMLNoSuchElementException("Tried to .nextElement() "
                                                + "with JMLValueBag "
                                                + "Enumerator `off the end'");
        }
    }

    /** Return a clone of this enumerator.
     */
    public /*@ non_null @*/ Object clone() {
        return new JMLValueBagEnumerator(abstractValue());
    } //@ nowarn Post;

    /** Return the abstract value of this bag enumerator.
     */
    protected /*@ pure non_null @*/ JMLValueBag abstractValue() {
        JMLValueBag absVal = currentBag;
        if (currentCount > 0) {
            absVal = currentBag.removeAll(currEntry).insert(currEntry,
                                                            currentCount);
        }
        return absVal;
    } //@ nowarn Exception;

    /** Return true just when this enumerator has the same state as
     * the given argument..
     */
    public boolean equals(/*@ nullable @*/ Object oth) {
        if  (oth == null || !(oth instanceof JMLValueBagEnumerator)) {
            return false;
        } else {
            JMLValueBagEnumerator jb = (JMLValueBagEnumerator) oth;
            return this.abstractValue().equals(jb.abstractValue());
        }
    }

    /** Return a hash code for this enumerator.
     */
    public int hashCode() {
        return abstractValue().hashCode();
    }
}
