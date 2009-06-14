
// @(#)$Id: ListIterator.spec 1299 2005-03-01 18:58:45Z erikpoll $

// Copyright (C) 2001, 2004 Iowa State University

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
 * @version $Revision: 1299 $
 * @author Gary T. Leavens
 */
public interface ListIterator extends Iterator {

    //@ model instance int cursor_position; in objectState;

    //@ public instance invariant 0 <= cursor_position;

    /*@ pure @*/ boolean hasNext();

    Object next();

    /*@ pure @*/ boolean hasPrevious();

    Object previous();

    /*@ pure @*/ int nextIndex();

    /*@ pure @*/ int previousIndex();


    // Modification Operations

    void remove();

    void set(Object o);

    void add(Object o);
}
