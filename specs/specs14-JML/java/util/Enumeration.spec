// @(#)$Id: Enumeration.spec,v 1.15 2005/12/06 19:55:00 chalin Exp $

// Adapted from Compaq SRC's ESC/Java

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

//@ model import org.jmlspecs.lang.JMLDataGroup;

/** JML's specification of java.util.Enumeration.
 * Some of this specification is taken from ESC/Java.
 * @version $Revision: 1.15 $
 * @author Gary T. Leavens
 */
public interface Enumeration {

    /** Do we have more elements?
     **/
    /*@ public model instance boolean moreElements;
      @                               in objectState;
      @*/

    /*@ public normal_behavior
      @    assignable objectState;
      @    ensures \result <==> moreElements;
      @*/
    boolean hasMoreElements();

    /** The type of the elements we return.
     **/
    //@ instance ghost public nullable \TYPE elementType;

    /** Do we ever return null as an element?
     **/
    //@ instance ghost public boolean returnsNull;

    /*@   public normal_behavior
      @     requires moreElements;
      @     assignable objectState;
      @     assignable moreElements;
      @     ensures (\result == null) || \typeof(\result) <: elementType;
      @     ensures !returnsNull ==> (\result != null);
      @ also
      @   public exceptional_behavior
      @     requires !moreElements;
      @     assignable \nothing;
      @     signals_only NoSuchElementException;
      @*/
    /*@ nullable @*/ Object nextElement();
}
