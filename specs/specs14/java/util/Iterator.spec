// @(#)$Id: Iterator.spec 1957 2006-06-08 17:45:06Z chalin $

// Adapted from Compaq SRC's specification for ESC/Java

// Copyright (C) 2001 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.util;

/** JML's specification of java.util.Iterator.
 * Some of this specification is taken from ESC/Java.
 * @version $Revision: 1957 $
 * @author Gary T. Leavens
 * @author Brandon Shilling
 * @author Joe Kiniry
 * @author David Cok
 */
public interface Iterator {

    /** Do we have more elements?
     **/
    /*@ public model instance boolean moreElements;
      @                               in objectState;
      @*/

    /** The type of the elements we return.
     **/
    //@ instance ghost public \TYPE elementType;

    /** Do we ever return null as an element?
     **/
    //@ instance ghost public boolean returnsNull;

    // !FIXME! - the aspect of the spec that an iterator is no longer
    // valid if the underlying collection is modified, besides via remove,
    // is not fully represented here.

    /** Has remove() been called since the last element was returned?
     *	It is initially false, since no element has yet been returned.
     **/
    //@ public instance ghost boolean remove_called_since = false;

    /*@ public normal_behavior
      @    assignable objectState;
      @    ensures \result <==> moreElements;
      @*/
    boolean hasNext();

    //+@ public invariant moreElements == hasNext(0);

    /*@ public normal_behavior
      @     requires n >= 0;
      @     ensures (* \result is true when this iterator
      @                 has n+1 more elements to return *);
      public pure model boolean hasNext(int n);  @*/

    /*@  public normal_behavior
      @     requires moreElements;
      @     assignable objectState, remove_called_since, moreElements;
      @     ensures !remove_called_since;
      @     ensures (\result == null) || \typeof(\result) <: elementType;
      @     ensures !returnsNull ==> (\result != null);
      @ also
      @   public exceptional_behavior
      @     requires !moreElements;
      @     assignable \nothing;
      @     signals_only NoSuchElementException;
      @*/
    Object next();

    /*@ public normal_behavior
      @    requires n >= 0 && hasNext(n);
      @    ensures (* \result is the nth, counting from 0,
      @             next element that would be returned by this iterator *);
      @    ensures !returnsNull ==> \result != null;
      @    ensures \result == null || \typeof(\result) <: elementType;
      @ for_example
      @    public normal_example
      @      requires n == 0 && moreElements;
      @      ensures (* \result == the object that would be
      @                 returned by calling next() *);
      public pure model Object nthNextElement(int n);  @*/

    /*@ public behavior
      @   assignable objectState, remove_called_since;
      @   ensures !\old(remove_called_since) && remove_called_since;
      @   signals_only RuntimeException;
      @   signals (UnsupportedOperationException);
      @   signals (IllegalStateException) \old(remove_called_since);
      @*/
    void remove();
}
