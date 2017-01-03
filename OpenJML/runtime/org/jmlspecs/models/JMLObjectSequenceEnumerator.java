// @(#)$Id: JMLSequenceEnumerator.java-generic,v 1.32 2005/12/24 21:20:31 chalin Exp $

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

/** An enumerator for sequences of objects.
 *
 * @version $Revision: 1.32 $
 * @author Gary T. Leavens, with help from Albert Baker, Clyde Ruby,
 * and others.
 * @see JMLEnumeration
 * @see JMLType
 * @see JMLObjectSequence
 * @see JMLValueSequence
 * @see JMLEnumerationToIterator
 */
// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class JMLObjectSequenceEnumerator
    implements JMLEnumeration, JMLObjectType
{

    /** The elements that have not yet been returned by nextElement.
     */
    //@ public model JMLObjectSequence uniteratedElems; in objectState;
    //@ public invariant uniteratedElems != null;

    /** The list representing the elements yet to be returned.
     */
    protected JMLListObjectNode currentNode;
    //@                               in uniteratedElems;

    /** The number of elements remaining to return.
     */
    protected /*@ spec_public @*/ int remaining;
    //@                                  in uniteratedElems;

    /*@ protected represents uniteratedElems
      @                  <- new JMLObjectSequence(currentNode, remaining);
      @*/

    //@ public invariant moreElements <==> remaining != 0;
    //@ public invariant remaining >= 0;
    //@ protected invariant currentNode == null <==> remaining == 0;

    //@ public invariant elementType <: \type(Object);

    /*@ public invariant
      @       !uniteratedElems.isEmpty()
      @        ==> uniteratedElems.elementType <: elementType;
      @*/

    //@ public constraint returnsNull == \old(returnsNull);

    /*@ public invariant
      @       !returnsNull
      @         ==> uniteratedElems.isEmpty() || !uniteratedElems.containsNull;
      @*/

    /** Initialize this with the given sequence.
     */
    /*@ normal_behavior
      @   requires s != null;
      @   assignable uniteratedElems;
      @   assignable  moreElements, elementType, returnsNull, owner;
      @   ensures uniteratedElems.equals(s);
      @   ensures owner == null;
      @   ensures elementType == s.elementType;
      @   ensures returnsNull == s.containsNull;
      @*/
    JMLObjectSequenceEnumerator(/*@ non_null @*/ JMLObjectSequence s) {
        //@ set owner = null;
        remaining = s.int_length();
        //@ set elementType = s.elementType;
        //@ set returnsNull = s.containsNull;
        currentNode = s.theSeq;
    }

    /** Tells whether this enumerator has more uniterated elements.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result == !uniteratedElems.isEmpty();
      @    ensures \result <==> remaining > 0;
      @*/
    public /*@ pure @*/ boolean hasMoreElements() {
        return currentNode != null;
    }

    /** Return the next element in the sequence, counting up, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     */
    /*@ also
      @  public normal_behavior
      @    requires hasMoreElements();
      @    assignable uniteratedElems, moreElements;
      @    ensures \old(uniteratedElems).itemAt(0) == \result
      @         && uniteratedElems.equals(\old(uniteratedElems).trailer());
      @ also
      @  public exceptional_behavior
      @    requires !hasMoreElements();
      @    assignable \nothing;
      @    signals (JMLNoSuchElementException);
      @ also
      @  protected normal_behavior 
      @    requires remaining > 0;
      @    assignable uniteratedElems, moreElements;
      @    assignable_redundantly currentNode, remaining;
      @    ensures currentNode == \old(currentNode.next)
      @         && remaining == \old(remaining - 1);
      @*/
    public Object nextElement() throws JMLNoSuchElementException {
        if (currentNode != null) {
            Object retValue = currentNode.val;
            currentNode = currentNode.next;
            remaining = remaining - 1;
            //@ assume currentNode == null <==> remaining == 0;
            //@ assume !returnsNull ==> retValue != null;
            //@ assume retValue != null ==> \typeof(retValue) <: elementType;
            return retValue;
        } else {
            throw new JMLNoSuchElementException("Tried to .nextElement() "
                                                + "with JMLObjectSequence "
                                                + "Enumerator `off the end'");
        }
    }

    /** Return a clone of this enumerator.
     */
    public /*@ non_null @*/ Object clone() {
        return
            new JMLObjectSequenceEnumerator(new JMLObjectSequence(currentNode,
                                                                  remaining));
    } //@ nowarn Post;

    /** Return true just when this enumerator has the same state as
     * the given argument..
     */
    public boolean equals(/*@ nullable @*/ Object oth) {
        if  (oth == null || !(oth instanceof JMLObjectSequenceEnumerator)) {
            return false;
        } else {
            JMLObjectSequenceEnumerator js
                = (JMLObjectSequenceEnumerator) oth;
            if (currentNode == null) {
                return js.currentNode == null;
            } else {
                return currentNode.equals(js.currentNode);
            }
        }
    }

    /** Return a hash code for this enumerator.
     */
    public int hashCode() {
        return currentNode == null ? 0 : currentNode.hashCode();
    }
}
