// @(#)$Id: JMLValueType.java,v 1.11 2005/12/23 17:02:06 chalin Exp $

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
                                                                              
/** Objects that contain values.
 * It is the intention that classes that implement JMLValueType provide a
 * "value semantics" for both clone() and equal(). Equality must be defined
 * by the ".equals()" for any objects contained within an instance of the
 * class. clone() must use the ".clone()" methods of any objects contained in
 * an instance of the class.
 * Hence, classes that implement JMLValueType have objects that are
 * "containers of values", in the sense that the user is interested
 * in the values referenced, not not simply the "addresses".
 *
 * @version $Revision: 1.11 $
 * @author Gary T. Leavens
 * @author Albert L. Baker
 * @see JMLType
 */
//@ pure
public interface JMLValueType extends JMLType {

    /** Return a deep copy of this object.
     */
    /*@ also 
      @   public normal_behavior
      @     ensures \result instanceof JMLValueType
      @      && (* all externally-visible mutable objects
      @            contained directly in "this" must be cloned in \result. *);
      @ implies_that
      @  ensures (* no direct aliases are created between this and \result *);
      @*/
    public /*@ pure @*/ Object clone();    


    /** Compare with ob2 using .equals on underlying objects.
     */
    /*@ also
      @  public normal_behavior
      @    ensures \result ==>
      @        ob2 != null
      @        && (* all externally-visible objects contained in ob2 test
      @              as ".equals()" to the corresponding object in this
      @              (and vice versa) *);
      @*/
    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object ob2);    
}
