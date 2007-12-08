// @(#)$Id: ListIterator.spec,v 1.16 2005/07/07 21:03:28 leavens Exp $

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


package java.util;

//@ model import org.jmlspecs.models.*;

/** JML's specification of java.util.Iterator.
 * Some of this specification is taken from ESC/Java.
 * @version $Revision: 1.16 $
 * @author Gary T. Leavens
 */
public interface ListIterator extends Iterator {

    //@ model instance int cursor_position; in objectState;

    //@ public instance invariant 0 <= cursor_position;

    /*@ public model instance JMLEqualsSequence previousElements;
      @                                              in cursor_position;
      @ public initially previousElements.isEmpty();
      @ public instance invariant previousElements != null;
      @*/

    //@ public instance represents cursor_position <- previousElements.int_size();

    /*@ pure @*/ boolean hasNext();

    /*@ also
      @ public normal_behavior
      @   requires hasNext();
      @   assignable objectState, remove_called_since, moreElements;
      @   ensures previousElements.equals(
      @          \old(previousElements).insertBack(\result));
      @*/
    Object next();

    /*@ public normal_behavior
      @   ensures \result <==> !previousElements.isEmpty();
      @*/
    /*@ pure @*/ boolean hasPrevious();

    /*@ public normal_behavior
      @   requires hasPrevious();
      @   assignable objectState, previousElements, remove_called_since;
      @   ensures \result == \old(previousElements.last())
      @        && previousElements.equals(\old(previousElements.header()));
      @   ensures !remove_called_since;
      @*/
    Object previous();

    /*@ public normal_behavior
      @   ensures \result == previousElements.int_size();
      @   ensures_redundantly \result == cursor_position;
      @*/
    /*@ pure @*/ int nextIndex();

    /*@ public normal_behavior
      @   ensures \result == previousElements.int_size() - 1;
      @   ensures_redundantly \result == cursor_position - 1;
      @*/
    /*@ pure @*/ int previousIndex();


    // Modification Operations
    
    /*@ also
      @   assignable objectState, remove_called_since;
      @   assignable previousElements;
      @   ensures previousElements.equals(previousElements.header());
      @   ensures_redundantly previousElements.int_size()
      @                       == \old(previousElements.int_size() - 1);
      @   ensures_redundantly cursor_position == \old(cursor_position - 1);
      @*/
    void remove();

    /*@ assignable objectState, previousElements;
      @ ensures previousElements.equals(
      @                  \old(previousElements.header().insertBack(o)));
      @ signals_only UnsupportedOperationException, ClassCastException,
      @              IllegalArgumentException, IllegalStateException;
      @ signals (IllegalStateException) \old(remove_called_since);
      @*/
    void set(Object o);

    /*@ assignable objectState, previousElements,
      @            remove_called_since;
      @ ensures remove_called_since;
      @ ensures previousElements.equals(
      @                  \old(previousElements.insertBack(o)));
      @ signals_only UnsupportedOperationException, ClassCastException,
      @              IllegalArgumentException;
      @*/
    void add(Object o);
}
