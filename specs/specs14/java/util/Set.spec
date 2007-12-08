// @(#)$Id: Set.spec 2226 2006-12-13 01:57:30Z chalin $

// Adapted in part from Compaq SRC's specification for ESC/Java

// Copyright (C) 2000, 2002 Iowa State University

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

/** JML's specification of java.util.Set.
 * @version $Revision: 2226 $
 * @author Brandon Shilling
 * @author Gary T. Leavens
 */
public interface Set extends Collection {

    /*@ public normal_behavior
      @   ensures \result;
      @ public pure model boolean initialSet();
      @*/

    // specification inherited
    int size();

    // specification inherited
    boolean isEmpty();

    // specification inherited
    boolean contains(/*@nullable*/ Object o);

    // specification inherited
    Iterator iterator();

    // specification inherited
    /*@non_null*/ Object[] toArray();

    // specification inherited
    /*@non_null*/ Object[] toArray(/*@non_null*/ Object[] a) throws NullPointerException;

    /*@ also
      @  public normal_behavior
      @    requires contains(o);
      @    requires !containsNull ==> o != null;
      @    requires  (o == null) || \typeof(o) <: elementType;
      @    assignable \nothing;
      @    ensures !\result;
      @*/
    boolean add(/*@nullable*/ Object o);

    /*@ also
       @ public normal_behavior
       @   requires contains(o);
       @   assignable objectState;
       @   ensures \result;
       @   ensures !contains(o);
       @*/
    boolean remove(/*@nullable*/ Object o);

    // Bulk Operations

    // specs are inherited
    //@ pure
    boolean containsAll(/*@non_null*/ Collection c) throws NullPointerException;

    // specs are inherited
    boolean addAll(/*@non_null*/ Collection c) throws NullPointerException;

    // specs are inherited
    boolean retainAll(/*@non_null*/ Collection c) throws NullPointerException;

    /*@ also public normal_behavior
       @   requires c != null;
       @   assignable objectState;
       @   ensures \old(c.contains(null)) ==> !contains(null);
       @   ensures (\forall Object o; c.contains(o) <==>
                      (\old(contains(o)) && !\old(c.contains(o))));
       @   ensures size() <= \old(size());
       @   ensures \result <==> size() != \old(size());
       @*/
    boolean removeAll(/*@non_null*/ Collection c) throws NullPointerException;

    // specification inherited
    void clear();

    // Comparison and hashing

    /*@ also public normal_behavior
       @   requires o != null;
       @   requires o instanceof Set;
       @   ensures \result <==>
               ((\forall Object oo; contains(oo) <==> ((Set)o).contains(oo))
             && contains(null) <==> ((Set)o).contains(null));
       @   ensures \result ==> (content.theSize == ((Set)o).content.theSize);
       @*/
    /*@ pure @*/ boolean equals(/*@nullable*/ Object o);

    // specification inherited
    int hashCode();
}
