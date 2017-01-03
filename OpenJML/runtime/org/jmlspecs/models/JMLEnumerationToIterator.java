// @(#)$Id: JMLEnumerationToIterator.java,v 1.27 2005/12/23 17:02:06 chalin Exp $

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

/** A wrapper that makes any {@link JMLEnumeration} into a {@link
 * JMLIterator} that does not support the remove operation.
 *
 * @version $Revision: 1.27 $
 * @author Gary T. Leavens
 * @see JMLEnumeration
 * @see JMLIterator
 * @see java.util.Iterator
 */
public class JMLEnumerationToIterator implements JMLIterator {

    protected final /*@ spec_public non_null @*/ JMLEnumeration theEnumeration;
    //@            maps theEnumeration.objectState \into objectState;

    /*@ public represents moreElements <- theEnumeration.hasMoreElements();
      @ public represents_redundantly
      @                   moreElements <- theEnumeration.moreElements;
      @*/

    /** Initialize this iterator with the given Enumeration.  The
     * enumeration is cloned.
     */
    /*@ public normal_behavior
      @   requires e != null;
      @   assignable owner, theEnumeration, elementType, moreElements;
      @   assignable returnsNull;
      @   ensures theEnumeration.equals(e);
      @   ensures owner == null;
      @*/
    //@ pure
    public JMLEnumerationToIterator(/*@ non_null @*/ JMLEnumeration e) {
        //@ set owner = null;
        Object o = e.clone();
        //@ assume o != null && o instanceof JMLEnumeration;
        theEnumeration = (JMLEnumeration) o;
        //@ assume theEnumeration.equals(e);
        //@ set elementType = e.elementType;
        //@ set returnsNull = e.returnsNull;
    }

    /** Tells whether this has more uniterated elements.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result == theEnumeration.moreElements;
      @     ensures_redundantly \result == theEnumeration.moreElements;
      @*/
    public /*@ pure @*/ boolean hasNext() {
        return theEnumeration.hasMoreElements();
    } //@ nowarn Post;

    /** Return the next element in this, if there is one.
     *  @exception JMLNoSuchElementException when this is empty.
     */
    /*@ also
      @   public normal_behavior
      @     requires moreElements;
      @     requires_redundantly hasNext();
      @     assignable objectState, moreElements, remove_called_since;
      @ also
      @   public exceptional_behavior
      @     requires !moreElements;
      @     requires_redundantly !hasNext();
      @     assignable \nothing;
      @     signals_only JMLNoSuchElementException;
      @*/
    public Object next() throws JMLNoSuchElementException {
        Object result = theEnumeration.nextElement();
        //@ set remove_called_since = false;
        return result;
    }

    /** The remove operation is not supported in this type.
     * So remove always throws an UnsupportedOperationException.
     */
    /*@ also
      @    signals_only UnsupportedOperationException;
      @*/
    public void remove() throws UnsupportedOperationException {
        throw new UnsupportedOperationException();
    }

    /** Return a clone of this iterator.
     */
    public /*@ pure @*/ Object clone() {
        Object o = theEnumeration.clone();
        //@ assume o != null && o instanceof JMLEnumeration;
        return new JMLEnumerationToIterator((JMLEnumeration) o);
    } //@ nowarn Post;

    /** Return true just when this iterator has the same state as
     * the given argument.
     */
    /*@ also
      @    public normal_behavior
      @      ensures \result <==> oth != null
      @           && oth instanceof JMLEnumerationToIterator
      @           && theEnumeration.equals(((JMLEnumerationToIterator) oth)
      @                                  .theEnumeration);
      @*/
    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object oth) {
        return oth != null
            && oth instanceof JMLEnumerationToIterator
            && theEnumeration.equals(((JMLEnumerationToIterator) oth)
                                     .theEnumeration);
    }

    /** Return a hash code for this iterator.
     */
    public /*@ pure @*/ int hashCode() {
        return theEnumeration.hashCode();
    }
}
